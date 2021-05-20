---
Título: 2ª propiedad semidistributiva de la intersección sobre la unión
Autor:  José A. Alonso
---

Demostrar que

> (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
sorry
</pre>

**Notas**

* En [este enlace](http://bit.ly/3hSB3Gz) se puede escribir las soluciones en Lean.
* A continuación se muestran algunas soluciones (que se pueden probar en [este enlace](http://bit.ly/3hMNR0K)).
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

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  intros x hx,
  cases hx with xst xsu,
  { split,
    { exact xst.1 },
    { left,
      exact xst.2 }},
  { split,
    { exact xsu.1 },
    { right,
      exact xsu.2 }},
end

-- 2ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  { use xs,
    left,
    exact xt },
  { use xs,
    right,
    exact xu },
end

-- 3ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by rw inter_distrib_left s t u

-- 4ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  intros x hx,
  finish
end
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2
imports Main
begin

(* 1ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof (rule subsetI)
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
  proof (rule UnE)
    assume xst : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ t"
      using xst by (simp only: IntD2)
    then have xtu : "x ∈ t ∪ u"
      by (simp only: UnI1)
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by (simp only: IntI)
  next
    assume xsu : "x ∈ s ∩ u"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ u"
      using xsu by (simp only: IntD2)
    then have xtu : "x ∈ t ∪ u"
      by (simp only: UnI2)
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by (simp only: IntI)
  qed
qed

(* 2ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
  proof
    assume xst : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by simp
    have xt : "x ∈ t"
      using xst by simp
    then have xtu : "x ∈ t ∪ u"
      by simp
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by simp
  next
    assume xsu : "x ∈ s ∩ u"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ u"
      using xsu by simp
    then have xtu : "x ∈ t ∪ u"
      by simp
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by simp
  qed
qed

(* 3ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
  proof
    assume "x ∈ s ∩ t"
    then show "x ∈ s ∩ (t ∪ u)"
      by simp
  next
    assume "x ∈ s ∩ u"
    then show "x ∈ s ∩ (t ∪ u)"
      by simp
  qed
qed

(* 4ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
    by auto
qed

(* 5ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
by auto

(* 6ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
by (simp only: distrib_inf_le)

end
</pre>
