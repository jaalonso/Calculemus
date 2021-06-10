---
Título: Imagen de la intersección mediante aplicaciones inyectivas
Autor:  José A. Alonso
---

Demostrar que si f es inyectiva, entonces
<pre lang="text">
   f[s] ∩ f[t] ⊆ f[s ∩ t]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry
</pre>

<h4>Soluciones</h4>
<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic

open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  intros y hy,
  cases hy  with hy1 hy2,
  cases hy1 with x1 hx1,
  cases hx1 with x1s fx1y,
  cases hy2 with x2 hx2,
  cases hx2 with x2t fx2y,
  use x1,
  split,
  { split,
    { exact x1s, },
    { convert x2t,
      apply h,
      rw ← fx2y at fx1y,
      exact fx1y, }},
  { exact fx1y, },
end

-- 2ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩,
  use x1,
  split,
  { split,
    { exact x1s, },
    { convert x2t,
      apply h,
      rw ← fx2y at fx1y,
      exact fx1y, }},
  { exact fx1y, },
end

-- 3ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩,
  unfold injective at h,
  finish,
end

-- 4ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by intro ; unfold injective at *  ; finish
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](https://bit.ly/3x9eUYK).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Imagen_de_la_interseccion_de_aplicaciones_inyectivas
imports Main
begin

(* 1ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` s ∩ f ` t"
  then have "y ∈ f ` s"
    by (rule IntD1)
  then show "y ∈ f ` (s ∩ t)"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s"
    have "x ∈ t"
    proof -
      have "y ∈ f ` t"
        using ‹y ∈ f ` s ∩ f ` t› by (rule IntD2)
      then show "x ∈ t"
      proof (rule imageE)
        fix z
        assume "y = f z"
        assume "z ∈ t"
        have "f x = f z"
          using ‹y = f x› ‹y = f z› by (rule subst)
        with ‹inj f› have "x = z"
          by (simp only: inj_eq)
        then show "x ∈ t"
          using ‹z ∈ t› by (rule ssubst)
      qed
    qed
    with ‹x ∈ s› have "x ∈ s ∩ t"
      by (rule IntI)
    with ‹y = f x› show "y ∈ f ` (s ∩ t)"
      by (rule image_eqI)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
proof
  fix y
  assume "y ∈ f ` s ∩ f ` t"
  then have "y ∈ f ` s" by simp
  then show "y ∈ f ` (s ∩ t)"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s"
    have "x ∈ t"
    proof -
      have "y ∈ f ` t" using ‹y ∈ f ` s ∩ f ` t› by simp
      then show "x ∈ t"
      proof
        fix z
        assume "y = f z"
        assume "z ∈ t"
        have "f x = f z" using ‹y = f x› ‹y = f z› by simp
        with ‹inj f› have "x = z" by (simp only: inj_eq)
        then show "x ∈ t" using ‹z ∈ t› by simp
      qed
    qed
    with ‹x ∈ s› have "x ∈ s ∩ t" by simp
    with ‹y = f x› show "y ∈ f ` (s ∩ t)" by simp
  qed
qed

(* 3ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
  using assms
  by (simp only: image_Int)

(* 4ª demostración *)

lemma
  assumes "inj f"
  shows "f ` s ∩ f ` t ⊆ f ` (s ∩ t)"
  using assms
  unfolding inj_def
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
