---
Título: Si a es un punto de acumulación de u, entonces ∀ε>0, ∀ N, ∃k≥N, |u(k)−a| < ε
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
También se puede definir que a es un límite de u por
<pre lang="text">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
</pre>

Los puntos de acumulación de una sucesión son los límites de sus subsucesiones. En Lean se puede definir por
<pre lang="text">
   def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
     ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
</pre>

Demostrar que si a es un punto de acumulación de u, entonces
<pre lang="text">
   ∀ ε > 0, ∀ N, ∃ k ≥ N, |u k - a| < ε
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}
variable  {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- En la demostración se usarán los siguientes lemas.

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

example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ k ≥ N, |u k - a| < ε :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}
variable  {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- En la demostración se usarán los siguientes lemas.

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

-- 1ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ k ≥ N, |u k - a| < ε :=
begin
  intros ε hε N,
  unfold punto_acumulacion at h,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  unfold limite at hφ2,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  clear hφ1 hφ2,
  use φ m,
  split,
  { exact hm', },
  { exact hN' m hm, },
end

-- 2ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  use φ m,
  exact ⟨hm', hN' m hm⟩,
end

-- 3ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  exact ⟨φ m, hm', hN' _ hm⟩,
end

-- 4ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  use φ m ; finish,
end

-- 5ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| < ε,
                  from hN' m hm1,
                show ∃ n ≥ N, |u n - a| < ε,
                  from exists.intro (φ m) (exists.intro hm2 h2)))))

-- 6ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| < ε,
                  from hN' m hm1,
                show ∃ n ≥ N, |u n - a| < ε,
                  from ⟨φ m, hm2, h2⟩))))

-- 7ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| < ε,
                  from hN' m hm1,
                ⟨φ m, hm2, h2⟩))))

-- 8ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                ⟨φ m, hm2, hN' m hm1⟩))))

-- 9ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 10ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          (λ m hm, exists.elim hm (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 11ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        exists.elim (aux2 hφ.1 N N')
          (λ m hm, exists.elim hm (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 12ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      (λ N' hN', exists.elim (aux2 hφ.1 N N')
        (λ m hm, exists.elim hm
          (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 13ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  (λ φ hφ, exists.elim (hφ.2 ε hε)
    (λ N' hN', exists.elim (aux2 hφ.1 N N')
      (λ m hm, exists.elim hm
        (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 14ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
λ ε hε N, exists.elim h
  (λ φ hφ, exists.elim (hφ.2 ε hε)
    (λ N' hN', exists.elim (aux2 hφ.1 N N')
      (λ m hm, exists.elim hm
        (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos"
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition punto_acumulacion :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "punto_acumulacion u a ⟷ (∃φ. extraccion φ ∧ limite (u ∘ φ) a)"

(* En la demostración se usarán los siguientes lemas *)
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

(* 1ª demostración *)
lemma
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
  obtain m where hm1 : "m ≥ N'" and hm2 : "φ m ≥ N"
    using aux2 hφ1 by blast
  have "φ m ≥ N ∧ ¦u (φ m) - a¦ < ε"
    using hN' hm1 hm2 by force
  then show "∃k≥N. ¦u k - a¦ < ε"
    by auto
qed

(* 2ª demostración *)
lemma
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

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
