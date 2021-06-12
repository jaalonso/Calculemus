---
Título: Imagen de la diferencia de conjuntos
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f[s] - f[t] ⊆ f[s - t]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  intros y hy,
  cases hy with yfs ynft,
  cases yfs with x hx,
  cases hx with xs fxy,
  use x,
  split,
  { split,
    { exact xs, },
    { dsimp,
      intro xt,
      apply ynft,
      rw ← fxy,
      apply mem_image_of_mem,
      exact xt, }},
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x, xs, fxy⟩, ynft⟩,
  use x,
  split,
  { split,
    { exact xs, },
    { intro xt,
      apply ynft,
      use [x, xt, fxy], }},
  { exact fxy, },
end

-- 3ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x, xs, fxy⟩, ynft⟩,
  use x,
  finish,
end

-- 4ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
subset_image_diff f s t
</pre>

Se puede interactuar con la prueba anterior en <a href="https://bit.ly/3wfAg6L" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_de_la_diferencia_de_conjuntos
imports Main
begin

(* 1ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
proof (rule subsetI)
  fix y
  assume hy : "y ∈ f ` s - f ` t"
  then show "y ∈ f ` (s - t)"
  proof (rule DiffE)
    assume "y ∈ f ` s"
    assume "y ∉ f ` t"
    note ‹y ∈ f ` s›
    then show "y ∈ f ` (s - t)"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x ∈ s"
      have ‹x ∉ t›
      proof (rule notI)
        assume "x ∈ t"
        then have "f x ∈ f ` t"
          by (rule imageI)
        with ‹y = f x› have "y ∈ f ` t"
          by (rule ssubst)
      with ‹y ∉ f ` t› show False
        by (rule notE)
    qed
    with ‹x ∈ s› have "x ∈ s - t"
      by (rule DiffI)
    then have "f x ∈ f ` (s - t)"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` (s - t)"
      by (rule ssubst)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
proof
  fix y
  assume hy : "y ∈ f ` s - f ` t"
  then show "y ∈ f ` (s - t)"
  proof
    assume "y ∈ f ` s"
    assume "y ∉ f ` t"
    note ‹y ∈ f ` s›
    then show "y ∈ f ` (s - t)"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s"
      have ‹x ∉ t›
      proof
        assume "x ∈ t"
        then have "f x ∈ f ` t" by simp
        with ‹y = f x› have "y ∈ f ` t" by simp
      with ‹y ∉ f ` t› show False by simp
    qed
    with ‹x ∈ s› have "x ∈ s - t" by simp
    then have "f x ∈ f ` (s - t)" by simp
    with ‹y = f x› show "y ∈ f ` (s - t)" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
  by (simp only: image_diff_subset)

(* 4ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
  by auto

end
</pre>
[/expand]

[expand title="Nuevas soluciones"]
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;lean&quot;&#62; (o &#60;pre lang=&quot;isar&quot;&#62;) y otra con &#60;/pre&#62;
</ul>
[/expand]
