---
Título: Imagen inversa de la unión
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f⁻¹[u ∪ v] = f⁻¹[u] ∪ f⁻¹[v]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
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

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { intros h,
    rw mem_preimage at h,
    cases h with fxu fxv,
    { left,
      apply mem_preimage.mpr,
      exact fxu, },
    { right,
      apply mem_preimage.mpr,
      exact fxv, }},
  { intro h,
    rw mem_preimage,
    cases h with xfu xfv,
    { rw mem_preimage at xfu,
      left,
      exact xfu, },
    { rw mem_preimage at xfv,
      right,
      exact xfv, }},
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { intros h,
    cases h with fxu fxv,
    { left,
      exact fxu, },
    { right,
      exact fxv, }},
  { intro h,
    cases h with xfu xfv,
    { left,
      exact xfu, },
    { right,
      exact xfv, }},
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { rintro (fxu | fxv),
    { exact or.inl fxu, },
    { exact or.inr fxv, }},
  { rintro (xfu | xfv),
    { exact or.inl xfu, },
    { exact or.inr xfv, }},
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { finish, },
  { finish, } ,
end

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  finish,
end

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext; finish

-- 7ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext; refl

-- 8ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
rfl

-- 9ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
preimage_union

-- 10ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by simp
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](https://bit.ly/3w9hIFh).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Imagen_inversa_de_la_union
imports Main
begin

(* 1ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
proof (rule equalityI)
  show "f -` (u ∪ v) ⊆ f -` u ∪ f -` v"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (u ∪ v)"
    then have "f x ∈ u ∪ v"
      by (rule vimageD)
    then show "x ∈ f -` u ∪ f -` v"
    proof (rule UnE)
      assume "f x ∈ u"
      then have "x ∈ f -` u"
        by (rule vimageI2)
      then show "x ∈ f -` u ∪ f -` v"
        by (rule UnI1)
    next
      assume "f x ∈ v"
      then have "x ∈ f -` v"
        by (rule vimageI2)
      then show "x ∈ f -` u ∪ f -` v"
        by (rule UnI2)
    qed
  qed
next
  show "f -` u ∪ f -` v ⊆ f -` (u ∪ v)"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` u ∪ f -` v"
    then show "x ∈ f -` (u ∪ v)"
    proof (rule UnE)
      assume "x ∈ f -` u"
      then have "f x ∈ u"
        by (rule vimageD)
      then have "f x ∈ u ∪ v"
        by (rule UnI1)
      then show "x ∈ f -` (u ∪ v)"
        by (rule vimageI2)
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v"
        by (rule vimageD)
      then have "f x ∈ u ∪ v"
        by (rule UnI2)
      then show "x ∈ f -` (u ∪ v)"
        by (rule vimageI2)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
proof
  show "f -` (u ∪ v) ⊆ f -` u ∪ f -` v"
  proof
    fix x
    assume "x ∈ f -` (u ∪ v)"
    then have "f x ∈ u ∪ v" by simp
    then show "x ∈ f -` u ∪ f -` v"
    proof
      assume "f x ∈ u"
      then have "x ∈ f -` u" by simp
      then show "x ∈ f -` u ∪ f -` v" by simp
    next
      assume "f x ∈ v"
      then have "x ∈ f -` v" by simp
      then show "x ∈ f -` u ∪ f -` v" by simp
    qed
  qed
next
  show "f -` u ∪ f -` v ⊆ f -` (u ∪ v)"
  proof
    fix x
    assume "x ∈ f -` u ∪ f -` v"
    then show "x ∈ f -` (u ∪ v)"
    proof
      assume "x ∈ f -` u"
      then have "f x ∈ u" by simp
      then have "f x ∈ u ∪ v" by simp
      then show "x ∈ f -` (u ∪ v)" by simp
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v" by simp
      then have "f x ∈ u ∪ v" by simp
      then show "x ∈ f -` (u ∪ v)" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
  by (simp only: vimage_Un)

(* 4ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
