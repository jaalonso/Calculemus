---
Título: Imagen inversa de la imagen de un conjunto
Autor:  José A. Alonso
---

Demostrar que si s es un subconjunto del dominio de la función f, entonces s está contenido en la [imagen inversa](https://bit.ly/3ckseBL) de la [imagen de s por f](https://bit.ly/3x2Jxij); es decir,
<pre lang="text">
   s ⊆ f⁻¹[f[s]]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α

example : s ⊆ f ⁻¹' (f '' s) :=
sorry
</pre>

<h4>Soluciones</h4>
<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α

-- 1ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  apply mem_preimage.mpr,
  apply mem_image_of_mem,
  exact xs,
end

-- 2ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  apply mem_image_of_mem,
  exact xs,
end

-- 3ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
λ x, mem_image_of_mem f

-- 4ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs],
end

-- 5ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  use [x, xs],
end

-- 6ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
subset_preimage_image f s
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](https://bit.ly/3fPCYKl).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Imagen_inversa_de_la_imagen
imports Main
begin

section ‹1ª demostración›

lemma "s ⊆ f -` (f ` s)"
proof (rule subsetI)
  fix x
  assume "x ∈ s"
  then have "f x ∈ f ` s"
    by (simp only: imageI)
  then show "x ∈ f -` (f ` s)"
    by (simp only: vimageI)
qed

section ‹2ª demostración›

lemma "s ⊆ f -` (f ` s)"
proof
  fix x
  assume "x ∈ s"
  then have "f x ∈ f ` s" by simp
  then show "x ∈ f -` (f ` s)" by simp
qed

section ‹3ª demostración›

lemma "s ⊆ f -` (f ` s)"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
