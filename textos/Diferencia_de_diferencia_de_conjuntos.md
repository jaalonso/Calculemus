---
Título: Diferencia de diferencia de conjuntos
Autor:  José A. Alonso
---

Demostrar que

> (s \ t) \ u ⊆ s \ (t ∪ u)

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
sorry
</pre>

**Notas**

* En [este enlace](https://bit.ly/3ynxFJx) se puede escribir las soluciones en Lean.
* A continuación se muestran algunas soluciones (que se pueden probar en [este enlace](https://bit.ly/3bxjzva)).
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

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs },
  { dsimp,
    intro xtu,
    cases xtu with xt xu,
    { show false, from xnt xt },
    { show false, from xnu xu }},
end

-- 2ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

-- 3ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  simp at *,
  finish,
end

-- 4ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  finish,
end

-- 5ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by rw diff_diff
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Diferencia_de_diferencia_de_conjuntos
imports Main
begin

(* 1ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ (s - t) - u"
  then show "x ∈ s - (t ∪ u)"
  proof (rule DiffE)
    assume xst : "x ∈ s - t"
    assume xnu : "x ∉ u"
    note xst
    then show "x ∈ s - (t ∪ u)"
    proof (rule DiffE)
      assume xs : "x ∈ s"
      assume xnt : "x ∉ t"
      have xntu : "x ∉ t ∪ u"
      proof (rule notI)
        assume xtu : "x ∈ t ∪ u"
        then show False
        proof (rule UnE)
          assume xt : "x ∈ t"
          with xnt show False
            by (rule notE)
        next
          assume xu : "x ∈ u"
          with xnu show False
            by (rule notE)
        qed
      qed
      show "x ∈ s - (t ∪ u)"
        using xs xntu by (rule DiffI)
    qed
  qed
qed

(* 2ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
proof
  fix x
  assume hx : "x ∈ (s - t) - u"
  then have xst : "x ∈ (s - t)"
    by simp
  then have xs : "x ∈ s"
    by simp
  have xnt : "x ∉ t"
    using xst by simp
  have xnu : "x ∉ u"
    using hx by simp
  have xntu : "x ∉ t ∪ u"
    using xnt xnu by simp
  then show "x ∈ s - (t ∪ u)"
    using xs by simp
qed

(* 3ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
proof
  fix x
  assume "x ∈ (s - t) - u"
  then show "x ∈ s - (t ∪ u)"
     by simp
qed

(* 4ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
by auto
</pre>
