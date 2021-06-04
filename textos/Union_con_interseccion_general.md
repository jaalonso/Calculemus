---
Título: Unión con intersección general
Autor:  José A. Alonso
---

Demostrar que
<pre lang="lean">
   s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variable  {α : Type}
variable  s : set α
variables A : ℕ → set α

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
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
variable  s : set α
variables A : ℕ → set α

-- 1ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { intros h i,
    cases h with xs xAi,
    { right,
      exact xs },
    { left,
      exact xAi i, }},
  { intro h,
    by_cases xs : x ∈ s,
    { left,
      exact xs },
    { right,
      intro i,
      cases h i with xAi xs,
      { exact xAi, },
      { contradiction, }}},
end

-- 2ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { rintros (xs | xI) i,
    { right,
      exact xs },
    { left,
      exact xI i }},
  { intro h,
    by_cases xs : x ∈ s,
    { left,
      exact xs },
    { right,
      intro i,
      cases h i,
      { assumption },
      { contradiction }}},
end

-- 3ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { finish, },
  { finish, },
end

-- 4ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext,
  simp only [mem_union, mem_Inter],
  split ; finish,
end

-- 5ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext,
  simp only [mem_union, mem_Inter],
  finish [iff_def],
end

-- 6ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by finish [ext_iff, mem_union, mem_Inter, iff_def]
</pre>

Se puede interactuar con la prueba anterior en [esta sesión con Lean](https://bit.ly/2SYrifu).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Union_con_interseccion_general
imports Main
begin

section ‹1ª demostración›

lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof (rule equalityI)
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof (rule UnE)
      assume "x ∈ s"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof (rule INT_I)
        fix i
        assume "i ∈ I"
        show "x ∈ A i ∪ s"
          using ‹x ∈ s› by (rule UnI2)
      qed
    next
      assume h1 : "x ∈ (⋂ i ∈ I. A i)"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof (rule INT_I)
        fix i
        assume "i ∈ I"
        with h1 have "x ∈ A i"
          by (rule INT_D)
        then show "x ∈ A i ∪ s"
          by (rule UnI1)
      qed
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof (rule subsetI)
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      assume "x ∈ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by (rule UnI1)
    next
      assume "x ∉ s"
      have "x ∈ (⋂ i ∈ I. A i)"
      proof (rule INT_I)
        fix i
        assume "i ∈ I"
        with h2 have "x ∈ A i ∪ s"
          by (rule INT_D)
        then show "x ∈ A i"
        proof (rule UnE)
          assume "x ∈ A i"
          then show "x ∈ A i"
            by this
        next
          assume "x ∈ s"
          with ‹x ∉ s› show "x ∈ A i"
            by (rule notE)
        qed
      qed
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by (rule UnI2)
    qed
  qed
qed

section ‹2ª demostración›

lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof
      assume "x ∈ s"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof
        fix i
        assume "i ∈ I"
        show "x ∈ A i ∪ s"
          using ‹x ∈ s› by simp
      qed
    next
      assume h1 : "x ∈ (⋂ i ∈ I. A i)"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof
        fix i
        assume "i ∈ I"
        with h1 have "x ∈ A i"
          by simp
        then show "x ∈ A i ∪ s"
          by simp
      qed
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      assume "x ∈ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by simp
    next
      assume "x ∉ s"
      have "x ∈ (⋂ i ∈ I. A i)"
      proof
        fix i
        assume "i ∈ I"
        with h2 have "x ∈ A i ∪ s"
          by (rule INT_D)
        then show "x ∈ A i"
        proof
          assume "x ∈ A i"
          then show "x ∈ A i"
            by this
        next
          assume "x ∈ s"
          with ‹x ∉ s› show "x ∈ A i"
            by simp
        qed
      qed
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by simp
    qed
  qed
qed

section ‹3ª demostración›

lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof
      assume "x ∈ s"
      then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
        by simp
    next
      assume "x ∈ (⋂ i ∈ I. A i)"
      then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
        by simp
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      assume "x ∈ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by simp
    next
      assume "x ∉ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        using h2 by simp
    qed
  qed
qed

section ‹4ª demostración›

lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof
      assume "x ∈ s"
      then show ?thesis by simp
    next
      assume "x ∈ (⋂ i ∈ I. A i)"
      then show ?thesis by simp
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis using h2 by simp
    qed
  qed
qed

section ‹5ª demostración›

lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
  by auto


end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
