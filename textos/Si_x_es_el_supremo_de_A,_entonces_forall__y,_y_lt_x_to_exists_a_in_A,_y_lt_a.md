---
Título: Si x es el supremo de A, entonces ∀ y, y < x → ∃ a ∈ A, y < a
Autor:  José A. Alonso
---

En Lean se puede definir que x es una cota superior de A por
<pre lang="text">
   def cota_superior (A : set ℝ) (x : ℝ) :=
     ∀ a ∈ A, a ≤ x
</pre>
y x es el supremo de A por
<pre lang="text">
   def es_supremo (A : set ℝ) (x : ℝ) :=
     cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y
</pre>

Demostrar que si x es el supremo de A, entonces
<pre lang="text">
   ∀ y, y < x → ∃ a ∈ A, y < a
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
variable {A : set ℝ}
variable {x : ℝ}

def cota_superior (A : set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def es_supremo (A : set ℝ) (x : ℝ) :=
  cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
variable {A : set ℝ}
variable {x : ℝ}

def cota_superior (A : set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def es_supremo (A : set ℝ) (x : ℝ) :=
  cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y

-- 1ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  by_contradiction,
  push_neg at h,
  have h1 : x ≤ y := hx.2 y h,
  replace h1 : ¬(y < x) := not_lt_of_le h1,
  exact h1 hy,
end

-- 2ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  by_contradiction,
  push_neg at h,
  apply absurd hy,
  apply not_lt_of_le,
  apply hx.2 y,
  exact h,
end

-- 3ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  by_contradiction,
  push_neg at h,
  exact absurd hy (not_lt_of_le (hx.2 y h)),
end

-- 4ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  contrapose hy,
  push_neg at hy,
  push_neg,
  unfold es_supremo at hx,
  cases hx with h1 h2,
  apply h2 y,
  unfold cota_superior,
  exact hy,
end

-- 5ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  contrapose hy,
  push_neg at hy,
  push_neg,
  cases hx with h1 h2,
  exact h2 y hy,
end

-- 6ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  contrapose hy,
  push_neg at hy,
  push_neg,
  exact hx.right y hy,
end

-- 7ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro y,
  contrapose!,
  exact hx.right y,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Si_x_es_el_supremo_de_A,_entonces_forall__y,_y_lt_x_to_exists_a_in_A,_y_lt_a.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Si_x_es_el_supremo_de_A,_entonces_forall__y,_y_lt_x_to_exists_a_in_A,_y_lt_a"
  imports Main HOL.Real
begin

definition cota_superior :: "(real set) ⇒ real ⇒ bool" where
  "cota_superior A x ⟷ (∀a∈A. a ≤ x)"

definition es_supremo :: "(real set) ⇒ real ⇒ bool" where
  "es_supremo A x ⟷ (cota_superior A x ∧
                       (∀ y. cota_superior A y ⟶ x ≤ y))"

(* 1ª demostración *)
lemma
  assumes "es_supremo A x"
  shows   "∀y<x. ∃a∈A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "∃a∈A. y < a"
  proof (rule ccontr)
    assume "¬ (∃a∈A. y < a)"
    then have "∀a∈A. a ≤ y"
      by auto
    then have "cota_superior A y"
      using cota_superior_def by simp
    then have "x ≤ y"
      using assms es_supremo_def by simp
    then have "x < x"
      using ‹y < x› by simp
    then show False by simp
  qed
qed

(* 2ª demostración *)
lemma
  assumes "es_supremo A x"
  shows   "∀y<x. ∃a∈A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "∃a∈A. y < a"
  proof (rule ccontr)
    assume "¬ (∃a∈A. y < a)"
    then have "cota_superior A y"
      using cota_superior_def by auto
    then show "False"
      using assms es_supremo_def ‹y < x› by auto
  qed
qed


end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
