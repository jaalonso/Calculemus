---
Título: Las funciones de extracción no están acotadas
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

Demostrar que las funciones de extracción no está acotadas; es decir, que si φ es una función de extracción, entonces
<pre lang="text">
    ∀ N N', ∃ n ≥ N', φ n ≥ N
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open nat

variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

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

example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open nat

variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

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
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  let n := max N N',
  use n,
  split,
  { exact le_max_right N N', },
  { calc N ≤ n   : le_max_left N N'
       ... ≤ φ n : aux h n, },
end

-- 2ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  let n := max N N',
  use n,
  split,
  { exact le_max_right N N', },
  { exact le_trans (le_max_left N N')
                   (aux h n), },
end

-- 3ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  use max N N',
  split,
  { exact le_max_right N N', },
  { exact le_trans (le_max_left N N')
                   (aux h (max N N')), },
end

-- 4ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  use max N N',
  exact ⟨le_max_right N N',
         le_trans (le_max_left N N')
                  (aux h (max N N'))⟩,
end

-- 5ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N',
  ⟨max N N', ⟨le_max_right N N',
              le_trans (le_max_left N N')
                       (aux h (max N N'))⟩⟩

-- 6ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
exists.intro n
  (exists.intro h1
    (show φ n ≥ N, from
       calc N ≤ n   : le_max_left N N'
          ... ≤ φ n : aux h n))

-- 7ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
⟨n, h1, calc N ≤ n   : le_max_left N N'
          ...  ≤ φ n : aux h n⟩

-- 8ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
⟨n, h1, le_trans (le_max_left N N')
                 (aux h (max N N'))⟩

-- 9ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
⟨n, h1, le_trans (le_max_left N N')
                 (aux h n)⟩

-- 10ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
⟨max N N', le_max_right N N',
           le_trans (le_max_left N N')
                    (aux h (max N N'))⟩

-- 11ª demostración
lemma extraccion_mye
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N',
  ⟨max N N', le_max_right N N',
             le_trans (le_max_left N N')
             (aux h (max N N'))⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_funciones_de_extraccion_no_estan_acotadas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_funciones_de_extraccion_no_estan_acotadas
imports Main
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

(* En la demostración se usará el siguiente lema *)
lemma aux :
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by simp
next
  fix n
  assume HI : "n ≤ φ n"
  also have "φ n < φ (Suc n)"
    using assms extraccion_def by blast
  finally show "Suc n ≤ φ (Suc n)"
    by simp
qed

(* 1ª demostración *)
lemma
  assumes "extraccion φ"
  shows   "∀ N N'. ∃ k ≥ N'. φ k ≥ N"
proof (intro allI)
  fix N N' :: nat
  let ?k = "max N N'"
  have "max N N' ≤ ?k"
    by (rule le_refl)
  then have hk : "N ≤ ?k ∧ N' ≤ ?k"
    by (simp only: max.bounded_iff)
  then have "?k ≥ N'"
    by (rule conjunct2)
  moreover
  have "N ≤ φ ?k"
  proof -
    have "N ≤ ?k"
      using hk by (rule conjunct1)
    also have "… ≤ φ ?k"
      using assms by (rule aux)
    finally show "N ≤ φ ?k"
      by this
  qed
  ultimately have "?k ≥ N' ∧ φ ?k ≥ N"
    by (rule conjI)
  then show "∃k ≥ N'. φ k ≥ N"
    by (rule exI)
qed

(* 2ª demostración *)
lemma
  assumes "extraccion φ"
  shows   "∀ N N'. ∃ k ≥ N'. φ k ≥ N"
proof (intro allI)
  fix N N' :: nat
  let ?k = "max N N'"
  have "?k ≥ N'"
    by simp
  moreover
  have "N ≤ φ ?k"
  proof -
    have "N ≤ ?k"
      by simp
    also have "… ≤ φ ?k"
      using assms by (rule aux)
    finally show "N ≤ φ ?k"
      by this
  qed
  ultimately show "∃k ≥ N'. φ k ≥ N"
    by blast
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
