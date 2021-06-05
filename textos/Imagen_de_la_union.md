---
Título: Imagen de la unión
Autor:  José A. Alonso
---

En Lean, la imagen de un conjunto s por una función f se representa por `f '' s`; es decir,
<pre lang="text">
   f '' s = {y | ∃ x, x ∈ s ∧ f x = y}
</pre>

Demostrar que
<pre lang="text">
   f '' (s ∪ t) = f '' s ∪ f '' t
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
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

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { intro h1,
    cases h1 with x hx,
    cases hx with xst fxy,
    rw ← fxy,
    cases xst with xs xt,
    { left,
      apply mem_image_of_mem,
      exact xs, },
    { right,
      apply mem_image_of_mem,
      exact xt, }},
  { intro h2,
    cases h2 with yfs yft,
    { cases yfs with x hx,
      cases hx with xs fxy,
      rw ← fxy,
      apply mem_image_of_mem,
      left,
      exact xs, },
    { cases yft with x hx,
      cases hx with xt fxy,
      rw ← fxy,
      apply mem_image_of_mem,
      right,
      exact xt, }},
end

-- 2ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, fxy⟩,
    rw ← fxy,
    cases xst with xs xt,
    { left,
      exact mem_image_of_mem f xs, },
    { right,
      exact mem_image_of_mem f xt, }},
  { rintros (yfs | yft),
    { rcases yfs with ⟨x, xs, fxy⟩,
      rw ← fxy,
      apply mem_image_of_mem,
      left,
      exact xs, },
    { rcases yft with ⟨x, xt, fxy⟩,
      rw ← fxy,
      apply mem_image_of_mem,
      right,
      exact xt, }},
end

-- 3ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, rfl⟩,
    cases xst with xs xt,
    { left,
      exact mem_image_of_mem f xs, },
    { right,
      exact mem_image_of_mem f xt, }},
  { rintros (yfs | yft),
    { rcases yfs with ⟨x, xs, rfl⟩,
      apply mem_image_of_mem,
      left,
      exact xs, },
    { rcases yft with ⟨x, xt, rfl⟩,
      apply mem_image_of_mem,
      right,
      exact xt, }},
end

-- 4ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, rfl⟩,
    cases xst with xs xt,
    { left,
      use [x, xs], },
    { right,
      use [x, xt], }},
  { rintros (yfs | yft),
    { rcases yfs with ⟨x, xs, rfl⟩,
      use [x, or.inl xs], },
    { rcases yft with ⟨x, xt, rfl⟩,
      use [x, or.inr xt], }},
end

-- 5ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left,
      use [x, xs] },
    { right,
      use [x, xt] }},
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
    { use [x, or.inl xs] },
    { use [x, or.inr xt] }},
end

-- 6ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { finish, },
    { finish, }},
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
    { finish, },
    { finish, }},
end

-- 7ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintros ⟨x, xs | xt, rfl⟩ ; finish, },
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩) ; finish, },
end

-- 8ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { finish, },
  { finish, },
end

-- 9ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  rw iff_def,
  finish,
end

-- 10ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by finish [ext_iff, iff_def, mem_image_eq]

-- 11ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
image_union f s t
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](https://bit.ly/34NvEbJ).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Imagen_de_la_union
imports Main
begin

section ‹1ª demostración›

lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
proof (rule equalityI)
  show "f ` (s ∪ t) ⊆ f ` s ∪ f ` t"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` (s ∪ t)"
    then show "y ∈ f ` s ∪ f ` t"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x ∈ s ∪ t"
      then show "y ∈ f ` s ∪ f ` t"
      proof (rule UnE)
        assume "x ∈ s"
        with ‹y = f x› have "y ∈ f ` s"
          by (simp only: image_eqI)
        then show "y ∈ f ` s ∪ f ` t"
          by (rule UnI1)
      next
        assume "x ∈ t"
        with ‹y = f x› have "y ∈ f ` t"
          by (simp only: image_eqI)
        then show "y ∈ f ` s ∪ f ` t"
          by (rule UnI2)
      qed
    qed
  qed
next
  show "f ` s ∪ f ` t ⊆ f ` (s ∪ t)"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` s ∪ f ` t"
    then show "y ∈ f ` (s ∪ t)"
    proof (rule UnE)
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∪ t)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x ∈ s"
        then have "x ∈ s ∪ t"
          by (rule UnI1)
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by (simp only: image_eqI)
      qed
    next
      assume "y ∈ f ` t"
      then show "y ∈ f ` (s ∪ t)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x ∈ t"
        then have "x ∈ s ∪ t"
          by (rule UnI2)
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by (simp only: image_eqI)
      qed
    qed
  qed
qed

section ‹2ª demostración›

lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
proof
  show "f ` (s ∪ t) ⊆ f ` s ∪ f ` t"
  proof
    fix y
    assume "y ∈ f ` (s ∪ t)"
    then show "y ∈ f ` s ∪ f ` t"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s ∪ t"
      then show "y ∈ f ` s ∪ f ` t"
      proof
        assume "x ∈ s"
        with ‹y = f x› have "y ∈ f ` s"
          by simp
        then show "y ∈ f ` s ∪ f ` t"
          by simp
      next
        assume "x ∈ t"
        with ‹y = f x› have "y ∈ f ` t"
          by simp
        then show "y ∈ f ` s ∪ f ` t"
          by simp
      qed
    qed
  qed
next
  show "f ` s ∪ f ` t ⊆ f ` (s ∪ t)"
  proof
    fix y
    assume "y ∈ f ` s ∪ f ` t"
    then show "y ∈ f ` (s ∪ t)"
    proof
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∪ t)"
      proof
        fix x
        assume "y = f x"
        assume "x ∈ s"
        then have "x ∈ s ∪ t"
          by simp
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by simp
      qed
    next
      assume "y ∈ f ` t"
      then show "y ∈ f ` (s ∪ t)"
      proof
        fix x
        assume "y = f x"
        assume "x ∈ t"
        then have "x ∈ s ∪ t"
          by simp
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by simp
      qed
    qed
  qed
qed

section ‹3ª demostración›

lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
  by (simp only: image_Un)

section ‹4ª demostración›

lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
