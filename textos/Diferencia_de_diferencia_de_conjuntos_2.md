---
Título: 2ª diferencia de diferencia de conjuntos
Autor:  José A. Alonso
---

Demostrar que

> s \ (t ∪ u) ⊆ (s \ t) \ u

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
sorry
</pre>

**Notas**

* En [este enlace](https://bit.ly/3u559sH) se puede escribir las soluciones en Lean.
* A continuación se muestran algunas soluciones (que se pueden probar en [este enlace](http://bit.ly/33YW7mz)).
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

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  intros x hx,
  split,
  { split,
    { exact hx.1, },
    { dsimp,
      intro xt,
      apply hx.2,
      left,
      exact xt, }},
  { dsimp,
    intro xu,
    apply hx.2,
    right,
    exact xu, },
end

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  split,
  { split,
    { exact xs, },
    { intro xt,
      exact xntu (or.inl xt), }},
  { intro xu,
    exact xntu (or.inr xu), },
end

-- 3ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  use xs,
  { intro xt,
    exact xntu (or.inl xt) },
  { intro xu,
    exact xntu (or.inr xu) },
end

-- 4ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩;
  finish,
end

-- 5ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by intro ; finish

-- 6ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by rw diff_diff
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Diferencia_de_diferencia_de_conjuntos_2
imports Main
begin

(* 1ª demostración *)
lemma "s - (t ∪ u) ⊆ (s - t) - u"
proof (rule subsetI)
  fix x
  assume "x ∈ s - (t ∪ u)"
  then show "x ∈ (s - t) - u"
  proof (rule DiffE)
    assume "x ∈ s"
    assume "x ∉ t ∪ u"
    have "x ∉ u"
    proof (rule notI)
      assume "x ∈ u"
      then have "x ∈ t ∪ u"
        by (simp only: UnI2)
      with ‹x ∉ t ∪ u› show False
        by (rule notE)
    qed
    have "x ∉ t"
    proof (rule notI)
      assume "x ∈ t"
      then have "x ∈ t ∪ u"
        by (simp only: UnI1)
      with ‹x ∉ t ∪ u› show False
        by (rule notE)
    qed
    with ‹x ∈ s› have "x ∈ s - t"
      by (rule DiffI)
    then show "x ∈ (s - t) - u"
      using ‹x ∉ u› by (rule DiffI)
  qed
qed

(* 2ª demostración *)
lemma "s - (t ∪ u) ⊆ (s - t) - u"
proof
  fix x
  assume "x ∈ s - (t ∪ u)"
  then show "x ∈ (s - t) - u"
  proof
    assume "x ∈ s"
    assume "x ∉ t ∪ u"
    have "x ∉ u"
    proof
      assume "x ∈ u"
      then have "x ∈ t ∪ u"
        by simp
      with ‹x ∉ t ∪ u› show False
        by simp
    qed
    have "x ∉ t"
    proof
      assume "x ∈ t"
      then have "x ∈ t ∪ u"
        by simp
      with ‹x ∉ t ∪ u› show False
        by simp
    qed
    with ‹x ∈ s› have "x ∈ s - t"
      by simp
    then show "x ∈ (s - t) - u"
      using ‹x ∉ u› by simp
  qed
qed

(* 3ª demostración *)
lemma "s - (t ∪ u) ⊆ (s - t) - u"
proof
  fix x
  assume "x ∈ s - (t ∪ u)"
  then show "x ∈ (s - t) - u"
  proof
    assume "x ∈ s"
    assume "x ∉ t ∪ u"
    then have "x ∉ u"
      by simp
    have "x ∉ t"
      using ‹x ∉ t ∪ u› by simp
    with ‹x ∈ s› have "x ∈ s - t"
      by simp
    then show "x ∈ (s - t) - u"
      using ‹x ∉ u› by simp
  qed
qed

(* 4ª demostración *)
lemma "s - (t ∪ u) ⊆ (s - t) - u"
proof
  fix x
  assume "x ∈ s - (t ∪ u)"
  then show "x ∈ (s - t) - u"
  proof
    assume "x ∈ s"
    assume "x ∉ t ∪ u"
    then show "x ∈ (s - t) - u"
      using ‹x ∈ s› by simp
  qed
qed

(* 5ª demostración *)
lemma "s - (t ∪ u) ⊆ (s - t) - u"
proof
  fix x
  assume "x ∈ s - (t ∪ u)"
  then show "x ∈ (s - t) - u"
    by simp
qed

(* 6ª demostración *)
lemma "s - (t ∪ u) ⊆ (s - t) - u"
by auto

end
</pre>
