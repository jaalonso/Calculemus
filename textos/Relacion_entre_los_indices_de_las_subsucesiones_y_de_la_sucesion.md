---
Título: Relación entre los índices de las subsucesiones y los de la sucesión
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
     ∀ {n m}, n < m → φ n < φ m
</pre>

Demostrar que si φ es una función de extracción, entonces
<pre lang="text">
   ∀ n, n ≤ φ n
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open nat

variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ {n m}, n < m → φ n < φ m

example :
  extraccion φ → ∀ n, n ≤ φ n :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open nat

variable {φ : ℕ → ℕ}

set_option pp.structure_projections false

def extraccion (φ : ℕ → ℕ) :=
  ∀ {n m}, n < m → φ n < φ m

-- 1ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    have h1 : m < succ m := lt_add_one m,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h h1, },
end

-- 2ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h (lt_add_one m), },
end

-- 3ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
assume h : extraccion φ,
assume n,
nat.rec_on n
  ( show 0 ≤ φ 0,
      from nat.zero_le (φ 0) )
  ( assume m,
    assume HI : m ≤ φ m,
    have h1 : m < succ m,
      from lt_add_one m,
    have h2 : m < φ (succ m), from
      calc m ≤ φ m        : HI
         ... < φ (succ m) : h h1,
    show succ m ≤ φ (succ m),
      from nat.succ_le_of_lt h2)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion
imports Main
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

(* En la demostración se usará el siguiente lema *)
lemma extraccionE:
  assumes "extraccion φ"
          "n < m"
  shows   "φ n < φ m"
proof -
  have "∀ n m. n < m ⟶ φ n < φ m"
    using assms(1) by (unfold extraccion_def)
  then have "n < m ⟶ φ n < φ m"
    by (elim allE)
  then show "φ n < φ m"
    using assms(2) by (rule mp)
qed

(* 1ª demostración *)
lemma
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by (rule le0)
next
  fix n
  assume "n ≤ φ n"
  also have "φ n < φ (Suc n)"
  proof -
    have "n < Suc n"
      by (rule lessI)
    with assms show "φ n < φ (Suc n)"
      by (rule extraccionE)
  qed
  finally show "Suc n ≤ φ (Suc n)"
    by (rule Suc_leI)
qed

(* 2ª demostración *)
lemma
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by (rule le0)
next
  fix n
  assume "n ≤ φ n"
  also have "… < φ (Suc n)"
  using assms
  proof (rule extraccionE)
    show "n < Suc n"
      by (rule lessI)
  qed
  finally show "Suc n ≤ φ (Suc n)"
    by (rule Suc_leI)
qed

(* 3ª demostración *)
lemma
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by (rule le0)
next
  fix n
  assume "n ≤ φ n"
  also have "… < φ (Suc n)"
    by (rule extraccionE [OF assms lessI])
  finally show "Suc n ≤ φ (Suc n)"
    by (rule Suc_leI)
qed

(* 4ª demostración *)
lemma
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

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
