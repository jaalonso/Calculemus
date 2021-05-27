---
Título: Diferencia de unión e interseccion
Autor:  José A. Alonso
---

Demostrar que

> (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
sorry
</pre>

<h4>Soluciones</h4>

<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

-- 1ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { split,
      { left,
        exact xs },
      { rintros ⟨_, xt⟩,
        contradiction }},
    { split ,
      { right,
        exact xt },
      { rintros ⟨xs, _⟩,
        contradiction }}},
  { rintros ⟨xs | xt, nxst⟩,
    { left,
      use xs,
      intro xt,
      apply nxst,
      split; assumption },
    { right,
      use xt,
      intro xs,
      apply nxst,
      split; assumption }},
end

-- 2ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { finish, },
    { finish, }},
  { rintros ⟨xs | xt, nxst⟩,
    { finish, },
    { finish, }},
end

-- 3ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩) ; finish, },
  { rintros ⟨xs | xt, nxst⟩ ; finish, },
end

-- 4ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext,
  split,
  { finish, },
  { finish, },
end

-- 5ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  rw ext_iff,
  intro,
  rw iff_def,
  finish,
end

-- 6ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by finish [ext_iff, iff_def]
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Diferencia_de_union_e_interseccion
imports Main
begin

section ‹1 demostración›

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof (rule equalityI)
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)"
    proof (rule UnE)
      assume "x ∈ s - t"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof (rule DiffE)
        assume "x ∈ s"
        assume "x ∉ t"
        have "x ∈ s ∪ t"
          using ‹x ∈ s› by (simp only: UnI1)
        moreover
        have "x ∉ s ∩ t"
        proof (rule notI)
          assume "x ∈ s ∩ t"
          then have "x ∈ t"
            by (simp only: IntD2)
          with ‹x ∉ t› show False
            by (rule notE)
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by (rule DiffI)
      qed
    next
      assume "x ∈ t - s"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof (rule DiffE)
        assume "x ∈ t"
        assume "x ∉ s"
        have "x ∈ s ∪ t"
          using ‹x ∈ t› by (simp only: UnI2)
        moreover
        have "x ∉ s ∩ t"
        proof (rule notI)
          assume "x ∈ s ∩ t"
          then have "x ∈ s"
            by (simp only: IntD1)
          with ‹x ∉ s› show False
            by (rule notE)
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by (rule DiffI)
      qed
    qed
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)"
    proof (rule DiffE)
      assume "x ∈ s ∪ t"
      assume "x ∉ s ∩ t"
      note ‹x ∈ s ∪ t›
      then show "x ∈ (s - t) ∪ (t - s)"
      proof (rule UnE)
        assume "x ∈ s"
        have "x ∉ t"
        proof (rule notI)
          assume "x ∈ t"
          with ‹x ∈ s› have "x ∈ s ∩ t"
            by (rule IntI)
          with ‹x ∉ s ∩ t› show False
            by (rule notE)
        qed
        with ‹x ∈ s› have "x ∈ s - t"
          by (rule DiffI)
        then show "x ∈ (s - t) ∪ (t - s)"
          by (simp only: UnI1)
      next
        assume "x ∈ t"
        have "x ∉ s"
        proof (rule notI)
          assume "x ∈ s"
          then have "x ∈ s ∩ t"
            using ‹x ∈ t› by (rule IntI)
          with ‹x ∉ s ∩ t› show False
            by (rule notE)
        qed
        with ‹x ∈ t› have "x ∈ t - s"
          by (rule DiffI)
        then show "x ∈ (s - t) ∪ (t - s)"
          by (rule UnI2)
      qed
    qed
  qed
qed

section ‹2 demostración›

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)"
    proof
      assume "x ∈ s - t"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof
        assume "x ∈ s"
        assume "x ∉ t"
        have "x ∈ s ∪ t"
          using ‹x ∈ s› by simp
        moreover
        have "x ∉ s ∩ t"
        proof
          assume "x ∈ s ∩ t"
          then have "x ∈ t"
            by simp
          with ‹x ∉ t› show False
            by simp
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by simp
      qed
    next
      assume "x ∈ t - s"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof
        assume "x ∈ t"
        assume "x ∉ s"
        have "x ∈ s ∪ t"
          using ‹x ∈ t› by simp
        moreover
        have "x ∉ s ∩ t"
        proof
          assume "x ∈ s ∩ t"
          then have "x ∈ s"
            by simp
          with ‹x ∉ s› show False
            by simp
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by simp
      qed
    qed
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)"
    proof
      assume "x ∈ s ∪ t"
      assume "x ∉ s ∩ t"
      note ‹x ∈ s ∪ t›
      then show "x ∈ (s - t) ∪ (t - s)"
      proof
        assume "x ∈ s"
        have "x ∉ t"
        proof
          assume "x ∈ t"
          with ‹x ∈ s› have "x ∈ s ∩ t"
            by simp
          with ‹x ∉ s ∩ t› show False
            by simp
        qed
        with ‹x ∈ s› have "x ∈ s - t"
          by simp
        then show "x ∈ (s - t) ∪ (t - s)"
          by simp
      next
        assume "x ∈ t"
        have "x ∉ s"
        proof
          assume "x ∈ s"
          then have "x ∈ s ∩ t"
            using ‹x ∈ t› by simp
          with ‹x ∉ s ∩ t› show False
            by simp
        qed
        with ‹x ∈ t› have "x ∈ t - s"
          by simp
        then show "x ∈ (s - t) ∪ (t - s)"
          by simp
      qed
    qed
  qed
qed

section ‹3ª demostración›

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)"
    proof
      assume "x ∈ s - t"
      then show "x ∈ (s ∪ t) - (s ∩ t)" by simp
    next
      assume "x ∈ t - s"
      then show "x ∈ (s ∪ t) - (s ∩ t)" by simp
    qed
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)"
    proof
      assume "x ∈ s ∪ t"
      assume "x ∉ s ∩ t"
      note ‹x ∈ s ∪ t›
      then show "x ∈ (s - t) ∪ (t - s)"
      proof
        assume "x ∈ s"
        then show "x ∈ (s - t) ∪ (t - s)"
          using ‹x ∉ s ∩ t› by simp
      next
        assume "x ∈ t"
        then show "x ∈ (s - t) ∪ (t - s)"
          using ‹x ∉ s ∩ t› by simp
      qed
    qed
  qed
qed

section ‹4ª demostración›

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)" by auto
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)" by auto
  qed
qed

section ‹5ª demostración›

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)" by auto
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)" by auto
qed

section ‹6ª demostración›

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
