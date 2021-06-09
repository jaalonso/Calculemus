---
Título: Imagen de la intersección
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f[s ∩ t] ⊆ f[s] ∩ f[t]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
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

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with xst fxy,
  split,
  { use x,
    split,
    { exact xst.1, },
    { exact fxy, }},
  { use x,
    split,
    { exact xst.2, },
    { exact fxy, }},
end

-- 2ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  intros y hy,
  rcases hy with ⟨x, ⟨xs, xt⟩, fxy⟩,
  split,
  { use x,
    exact ⟨xs, fxy⟩, },
  { use x,
    exact ⟨xt, fxy⟩, },
end

-- 3ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x, ⟨xs, xt⟩, fxy⟩,
  split,
  { use [x, xs, fxy], },
  { use [x, xt, fxy], },
end

-- 4ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
image_inter_subset f s t

-- 5ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by intro ; finish
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](https://bit.ly/3v6aWPk).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Imagen_de_la_interseccion
imports Main
begin

section ‹1ª demostración›

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` (s ∩ t)"
  then have "y ∈ f ` s"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ s"
      using ‹x ∈ s ∩ t› by (rule IntD1)
    then have "f x ∈ f ` s"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` s"
      by (rule ssubst)
  qed
  moreover
  note ‹y ∈ f ` (s ∩ t)›
  then have "y ∈ f ` t"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ t"
      using ‹x ∈ s ∩ t› by (rule IntD2)
    then have "f x ∈ f ` t"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` t"
      by (rule ssubst)
  qed
  ultimately show "y ∈ f ` s ∩ f ` t"
    by (rule IntI)
qed

section ‹2ª demostración›

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
proof
  fix y
  assume "y ∈ f ` (s ∩ t)"
  then have "y ∈ f ` s"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ s"
      using ‹x ∈ s ∩ t› by simp
    then have "f x ∈ f ` s"
      by simp
    with ‹y = f x› show "y ∈ f ` s"
      by simp
  qed
  moreover
  note ‹y ∈ f ` (s ∩ t)›
  then have "y ∈ f ` t"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ t"
      using ‹x ∈ s ∩ t› by simp
    then have "f x ∈ f ` t"
      by simp
    with ‹y = f x› show "y ∈ f ` t"
      by simp
  qed
  ultimately show "y ∈ f ` s ∩ f ` t"
    by simp
qed

section ‹3ª demostración›

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
proof
  fix y
  assume "y ∈ f ` (s ∩ t)"
  then obtain x where hx : "y = f x ∧ x ∈ s ∩ t" by auto
  then have "y = f x" by simp
  have "x ∈ s" using hx by simp
  have "x ∈ t" using hx by simp
  have "y ∈  f ` s" using ‹y = f x› ‹x ∈ s› by simp
  moreover
  have "y ∈  f ` t" using ‹y = f x› ‹x ∈ t› by simp
  ultimately show "y ∈ f ` s ∩ f ` t"
    by simp
qed

section ‹4ª demostración›

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
  by (simp only: image_Int_subset)

section ‹5ª demostración›

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
