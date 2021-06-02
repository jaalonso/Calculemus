---
Título: Intersección de intersecciones
Autor:  José A. Alonso
---

Demostrar que
<pre lang="lean">
(⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variable  {α : Type}
variables A B : ℕ → set α

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
sorry
</pre>

<h4>Soluciones</h4>
<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
import tactic

open set

variable  {α : Type}
variables A B : ℕ → set α

-- 1ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    { intro i,
      exact (h i).2 }},
  { intros h i,
    cases h with h1 h2,
    split,
    { exact h1 i },
    { exact h2 i }},
end

-- 2ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  exact ⟨λ h, ⟨λ i, (h i).1, λ i, (h i).2⟩,
         λ ⟨h1, h2⟩ i, ⟨h1 i, h2 i⟩⟩,
end

-- 3ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext,
  simp only [mem_inter_eq, mem_Inter],
  finish,
end

-- 4ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext,
  finish [mem_inter_eq, mem_Inter],
end

-- 5ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by finish [mem_inter_eq, mem_Inter, ext_iff]
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](???).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Interseccion_de_intersecciones
imports Main
begin

section ‹1ª demostración›

lemma "(⋂ i ∈ I. A i ∩ B i) = (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
proof (rule equalityI)
  show "(⋂ i ∈ I. A i ∩ B i) ⊆ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
  proof (rule subsetI)
    fix x
    assume h1 : "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    have "x ∈ (⋂ i ∈ I. A i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      with h1 have "x ∈ A i ∩ B i"
        by (rule INT_D)
      then show "x ∈ A i"
        by (rule IntD1)
    qed
    moreover
    have "x ∈ (⋂ i ∈ I. B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      with h1 have "x ∈ A i ∩ B i"
        by (rule INT_D)
      then show "x ∈ B i"
        by (rule IntD2)
    qed
    ultimately show "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
      by (rule IntI)
  qed
next
  show "(⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. A i ∩ B i)"
  proof (rule subsetI)
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      have "x ∈ A i"
      proof -
        have "x ∈ (⋂ i ∈ I. A i)"
          using h2 by (rule IntD1)
        then show "x ∈ A i"
          using ‹i ∈ I› by (rule INT_D)
      qed
      moreover
      have "x ∈ B i"
      proof -
        have "x ∈ (⋂ i ∈ I. B i)"
          using h2 by (rule IntD2)
        then show "x ∈ B i"
          using ‹i ∈ I› by (rule INT_D)
      qed
      ultimately show "x ∈ A i ∩ B i"
        by (rule IntI)
    qed
  qed
qed

section ‹2ª demostración›

lemma "(⋂ i ∈ I. A i ∩ B i) = (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
proof
  show "(⋂ i ∈ I. A i ∩ B i) ⊆ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
  proof
    fix x
    assume h1 : "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    have "x ∈ (⋂ i ∈ I. A i)"
    proof
      fix i
      assume "i ∈ I"
      then show "x ∈ A i"
        using h1 by simp
    qed
    moreover
    have "x ∈ (⋂ i ∈ I. B i)"
    proof
      fix i
      assume "i ∈ I"
      then show "x ∈ B i"
        using h1 by simp
    qed
    ultimately show "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
      by simp
  qed
next
  show "(⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. A i ∩ B i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    proof
      fix i
      assume "i ∈ I"
      then have "x ∈ A i"
        using h2 by simp
      moreover
      have "x ∈ B i"
        using ‹i ∈ I› h2 by simp
      ultimately show "x ∈ A i ∩ B i"
        by simp
    qed
qed
qed

section ‹3ª demostración›

lemma "(⋂ i ∈ I. A i ∩ B i) = (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
