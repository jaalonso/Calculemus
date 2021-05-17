---
Título: Propiedad semidistributiva de la intersección sobre la unión
Autor:  José A. Alonso
---

Demostrar que

> s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
sorry
</pre>

**Notas**

* En [este enlace](https://bit.ly/3uWFUtF) se puede escribir las soluciones en Lean.
* A continuación se muestran algunas soluciones (que se pueden probar en [este enlace](https://bit.ly/3uYXTjs)).
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

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  clear hx,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  { right,
    show x ∈ s ∩ u,
    exact ⟨xs, xu⟩ },
end

-- 2ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left,
    exact ⟨xs, xt⟩ },
  { right,
    exact ⟨xs, xu⟩ },
end

-- 3ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  by finish
end

-- 4ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by rw inter_union_distrib_left

</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Propiedad_semidistributiva_de_la_interseccion_sobre_la_union
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by (simp only: IntD1)
  have xtu: "x ∈ t ∪ u"
    using hx by (simp only: IntD2)
  then have "x ∈ t ∨ x ∈ u"
    by (simp only: Un_iff)
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule disjE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI1)
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI2)
  qed
qed

(* 2ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by simp
  have xtu: "x ∈ t ∪ u"
    using hx by simp
  then have "x ∈ t ∨ x ∈ u"
    by simp
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by (simp only: IntD1)
  have xtu: "x ∈ t ∪ u"
    using hx by (simp only: IntD2)
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule UnE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI1)
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI2)
  qed
qed

(* 4ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by simp
  have xtu: "x ∈ t ∪ u"
    using hx by simp
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule UnE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  qed
qed

(* 5ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
by (simp only: Int_Un_distrib)

(* 6ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
by auto

end
</pre>
