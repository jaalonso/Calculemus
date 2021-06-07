---
Título: Monotonía de la imagen de conjuntos
Autor:  José A. Alonso
---

Demostrar que si s ⊆ t, entonces
<pre lang="text">
    f[s] ⊆ f[t]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
sorry
</pre>

<h4>Soluciones</h4>
<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  intros y hy,
  rw mem_image at hy,
  cases hy with x hx,
  cases hx with xs fxy,
  use x,
  split,
  { exact h xs, },
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  intros y hy,
  rcases hy with ⟨x, xs, fxy⟩,
  use x,
  exact ⟨h xs, fxy⟩,
end

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x, xs, fxy ⟩,
  use [x, h xs, fxy],
end

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by finish [subset_def, mem_image_eq]

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
image_subset f h
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](https://bit.ly/3x3Gjew).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Monotonia_de_la_imagen_de_conjuntos
imports Main
begin

section ‹1ª demostración›

lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` s"
  then show "y ∈ f ` t"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s"
    then have "x ∈ t"
      using ‹s ⊆ t› by (simp only: set_rev_mp)
    then have "f x ∈ f ` t"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` t"
      by (rule ssubst)
  qed
qed

section ‹2ª demostración›

lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
proof
  fix y
  assume "y ∈ f ` s"
  then show "y ∈ f ` t"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s"
    then have "x ∈ t"
      using ‹s ⊆ t› by (simp only: set_rev_mp)
    then have "f x ∈ f ` t"
      by simp
    with ‹y = f x› show "y ∈ f ` t"
      by simp
  qed
qed

section ‹3ª demostración›

lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
  using assms
  by blast

section ‹4ª demostración›

lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
  using assms
  by (simp only: image_mono)

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
