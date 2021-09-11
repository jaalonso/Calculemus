---
Título: Pruebas de "(∀ ε > 0, y ≤ x + ε) → y ≤ x"
Autor:  José A. Alonso
---

Sean x, y ∈ ℝ. Demostrar que
<pre lang="text">
   (∀ ε > 0, y ≤ x + ε) →  y ≤ x
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables {x y : ℝ}

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables {x y : ℝ}

-- 1ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
  { apply half_pos,
    exact sub_pos.mpr h, },
  { calc x + (y - x) / 2
         = (x + y) / 2   : by ring_nf
     ... < (y + y) / 2   : div_lt_div_of_lt zero_lt_two (add_lt_add_right h y)
     ... = (2 * y) / 2   : congr_arg2 (/) (two_mul y).symm rfl
     ... = y             : by ring_nf, },
end

-- 2ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
  { exact half_pos (sub_pos.mpr h), },
  { calc x + (y - x) / 2
         = (x + y) / 2   : by ring_nf
     ... < (y + y) / 2   : by linarith
     ... = (2 * y) / 2   : by ring_nf
     ... = y             : by ring_nf, },
end

-- 3ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
  { linarith },
  { linarith },
end

-- 4ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split ; linarith,
end

-- 5ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  intro h1,
  by_contradiction h2,
  replace h2 : x < y := not_le.mp h2,
  rcases (exists_between h2) with ⟨z, h3, h4⟩,
  replace h3 : 0 < z - x := sub_pos.mpr h3,
  replace h1 : y ≤ x + (z - x) := h1 (z - x) h3,
  replace h1 : y ≤ z := by finish,
  have h4 : y < y := gt_of_gt_of_ge h4 h1,
  exact absurd h4 (irrefl y),
end

-- 6ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  intro h1,
  by_contradiction h2,
  replace h2 : x < y := not_le.mp h2,
  rcases (exists_between h2) with ⟨z, hxz, hzy⟩,
  apply lt_irrefl y,
  calc y ≤ x + (z - x) : h1 (z - x) (sub_pos.mpr hxz)
     ... = z           : by ring
     ... < y           : hzy,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/CS_de_y_le_x.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory CS_de_y_le_x
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes x y :: real
  shows "(∀ε>0. y ≤ x + ε) ⟶ y ≤ x"
proof (rule impI)
  assume h1 : "(∀ε>0. y ≤ x + ε)"
  show "y ≤ x"
  proof (rule ccontr)
    assume "¬ (y ≤ x)"
    then have "x < y"
      by simp
    then have "(y - x) / 2 > 0"
      by simp
    then have "y ≤ x + (y - x) / 2"
      using h1 by blast
    then have "2 * y ≤ 2 * x + (y - x)"
      by argo
    then have "y ≤ x"
      by simp
    then show False
      using ‹¬ (y ≤ x)› by simp
  qed
qed

(* 2ª demostración *)
lemma
  fixes x y :: real
  shows "(∀ε>0. y ≤ x + ε) ⟶ y ≤ x"
proof (rule impI)
  assume h1 : "(∀ε>0. y ≤ x + ε)"
  show "y ≤ x"
  proof (rule ccontr)
    assume "¬ (y ≤ x)"
    then have "x < y"
      by simp
    then obtain z where hz : "x < z ∧ z < y"
      using Rats_dense_in_real by blast
    then have "0 < z -x"
      by simp
    then have "y ≤ x + (z - x)"
      using h1 by blast
    then have "y ≤ z"
      by simp
    then show False
      using hz by simp
  qed
qed

(* 3ª demostración *)
lemma
  fixes x y :: real
  shows "(∀ε>0. y ≤ x + ε) ⟶ y ≤ x"
proof (rule impI)
  assume h1 : "(∀ε>0. y ≤ x + ε)"
  show "y ≤ x"
  proof (rule dense_le)
    fix z
    assume "z < y"
    then have "0 < y - z"
      by simp
    then have "y ≤ x + (y - z)"
      using h1 by simp
    then have "0 ≤ x - z"
      by simp
    then show "z ≤ x"
      by simp
  qed
qed

(* 4ª demostración *)
lemma
  fixes x y :: real
  shows "(∀ε>0. y ≤ x + ε) ⟶ y ≤ x"
  by (simp add: field_le_epsilon)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
