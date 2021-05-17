---
title:  Propiedad de monotonía de la intersección.
author: José A. Alonso Jiménez
date:   Sevilla, 17 de mayo de 2021
---

Demostrar que la intersección es monótona por la izquierda; es decir, si

> s ⊆ t,

entonces

> s ∩ u ⊆ t ∩ u.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
sorry
</pre>

**Notas**

* En [este enlace](https://bit.ly/3frC0T0) se puede escribir las soluciones en Lean.
* A continuación se muestran algunas soluciones (que se pueden probar en [este enlace](https://bit.ly/3tZEP3i)).
* En los comentarios se pueden publicar otras soluciones, en Lean o en otros sistemas de razonamiento.
  + Para publicar las demostraciones en Lean se deben de escribir entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
  + Para publicar las demostraciones en Isabelle/HOL se deben de escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw subset_def,
  rw inter_def,
  rw inter_def,
  dsimp,
  intros x h,
  cases h with xs xu,
  split,
  { rw subset_def at h,
    apply h,
    assumption },
  { assumption },
end

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  dsimp,
  rintros x ⟨xs, xu⟩,
  rw subset_def at h,
  exact ⟨h _ xs, xu⟩,
end

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩,
end

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
inter_subset_inter_left u h
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Propiedad_de_monotonia_de_la_interseccion
imports Main
begin

(* 1ª solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
proof  (rule subsetI)
  fix x
  assume hx: "x ∈ s ∩ u"
  have xs: "x ∈ s"
    using hx
    by (simp only: IntD1)
  then have xt: "x ∈ t"
    using assms
    by (simp only: subset_eq)
  have xu: "x ∈ u"
    using hx
    by (simp only: IntD2)
  show "x ∈ t ∩ u"
    using xt xu
    by (simp only: Int_iff)
qed

(* 2 solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
proof
  fix x
  assume hx: "x ∈ s ∩ u"
  have xs: "x ∈ s"
    using hx
    by simp
  then have xt: "x ∈ t"
    using assms
    by auto
  have xu: "x ∈ u"
    using hx
    by simp
  show "x ∈ t ∩ u"
    using xt xu
    by simp
qed

(* 3ª solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
using assms
by auto

(* 4ª solución *)
lemma
  "s ⊆ t ⟹ s ∩ u ⊆ t ∩ u"
by auto

end
</pre>
