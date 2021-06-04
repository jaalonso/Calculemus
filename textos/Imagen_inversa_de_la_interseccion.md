---
Título: Imagen inversa de la intersección
Autor:  José A. Alonso
---

En Lean, la imagen inversa de un conjunto s (de elementos de tipo β)
por la función f (de tipo α → β) es el conjunto `f ⁻¹' s` de
elementos x (de tipo α) tales que `f x ∈ s`.

Demostrar que
<pre lang="text">
   f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
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
variables u v : set β

-- 1ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext x,
  split,
  { intro h,
    split,
    { apply mem_preimage.mpr,
      rw mem_preimage at h,
      exact mem_of_mem_inter_left h, },
    { apply mem_preimage.mpr,
      rw mem_preimage at h,
      exact mem_of_mem_inter_right h, }},
  { intro h,
    apply mem_preimage.mpr,
    split,
    { apply mem_preimage.mp,
      exact mem_of_mem_inter_left h,},
    { apply mem_preimage.mp,
      exact mem_of_mem_inter_right h, }},
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext x,
  exact ⟨λ h, ⟨mem_preimage.mpr (mem_of_mem_inter_left h),
               mem_preimage.mpr (mem_of_mem_inter_right h)⟩,
         λ h, ⟨mem_preimage.mp (mem_of_mem_inter_left h),
               mem_preimage.mp (mem_of_mem_inter_right h)⟩⟩,
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext,
  refl,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by {ext, refl}

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
rfl

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
preimage_inter
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](???).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Imagen_inversa_de_la_interseccion
imports Main
begin

section ‹1ª demostración›

lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
proof (rule equalityI)
  show "f -` (u ∩ v) ⊆ f -` u ∩ f -` v"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (u ∩ v)"
    then have h : "f x ∈ u ∩ v"
      by (simp only: vimage_eq)
    have "x ∈ f -` u"
    proof -
      have "f x ∈ u"
        using h by (rule IntD1)
      then show "x ∈ f -` u"
        by (rule vimageI2)
    qed
    moreover
    have "x ∈ f -` v"
    proof -
      have "f x ∈ v"
        using h by (rule IntD2)
      then show "x ∈ f -` v"
        by (rule vimageI2)
    qed
    ultimately show "x ∈ f -` u ∩ f -` v"
      by (rule IntI)
  qed
next
  show "f -` u ∩ f -` v ⊆ f -` (u ∩ v)"
  proof (rule subsetI)
    fix x
    assume h2 : "x ∈ f -` u ∩ f -` v"
    have "f x ∈ u"
    proof -
      have "x ∈ f -` u"
        using h2 by (rule IntD1)
      then show "f x ∈ u"
        by (rule vimageD)
    qed
    moreover
    have "f x ∈ v"
    proof -
      have "x ∈ f -` v"
        using h2 by (rule IntD2)
      then show "f x ∈ v"
        by (rule vimageD)
    qed
    ultimately have "f x ∈ u ∩ v"
      by (rule IntI)
    then show "x ∈ f -` (u ∩ v)"
      by (rule vimageI2)
  qed
qed

section ‹2ª demostración›

lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
proof
  show "f -` (u ∩ v) ⊆ f -` u ∩ f -` v"
  proof
    fix x
    assume "x ∈ f -` (u ∩ v)"
    then have h : "f x ∈ u ∩ v"
      by simp
    have "x ∈ f -` u"
    proof -
      have "f x ∈ u"
        using h by simp
      then show "x ∈ f -` u"
        by simp
    qed
    moreover
    have "x ∈ f -` v"
    proof -
      have "f x ∈ v"
        using h by simp
      then show "x ∈ f -` v"
        by simp
    qed
    ultimately show "x ∈ f -` u ∩ f -` v"
      by simp
  qed
next
  show "f -` u ∩ f -` v ⊆ f -` (u ∩ v)"
  proof
    fix x
    assume h2 : "x ∈ f -` u ∩ f -` v"
    have "f x ∈ u"
    proof -
      have "x ∈ f -` u"
        using h2 by simp
      then show "f x ∈ u"
        by simp
    qed
    moreover
    have "f x ∈ v"
    proof -
      have "x ∈ f -` v"
        using h2 by simp
      then show "f x ∈ v"
        by simp
    qed
    ultimately have "f x ∈ u ∩ v"
      by simp
    then show "x ∈ f -` (u ∩ v)"
      by simp
  qed
qed

section ‹3ª demostración›

lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
proof
  show "f -` (u ∩ v) ⊆ f -` u ∩ f -` v"
  proof
    fix x
    assume h1 : "x ∈ f -` (u ∩ v)"
    have "x ∈ f -` u" using h1 by simp
    moreover
    have "x ∈ f -` v" using h1 by simp
    ultimately show "x ∈ f -` u ∩ f -` v" by simp
  qed
next
  show "f -` u ∩ f -` v ⊆ f -` (u ∩ v)"
  proof
    fix x
    assume h2 : "x ∈ f -` u ∩ f -` v"
    have "f x ∈ u" using h2 by simp
    moreover
    have "f x ∈ v" using h2 by simp
    ultimately have "f x ∈ u ∩ v" by simp
    then show "x ∈ f -` (u ∩ v)" by simp
  qed
qed

section ‹4ª demostración›

lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
  by (simp only: vimage_Int)

section ‹5ª demostración›

lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
