---
Título: Unión con su diferencia
Autor:  José A. Alonso
---

Demostrar que

> (s \ t) ∪ t = s ∪ t

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

example : (s \ t) ∪ t = s ∪ t :=
sorry
</pre>

<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

-- 1ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x,
  split,
  { intro hx,
    cases hx with xst xt,
    { left,
      exact xst.1, },
    { right,
      exact xt }},
  { by_cases h : x ∈ t,
    { intro _,
      right,
      exact h },
    { intro hx,
      cases hx with xs xt,
      { left,
        split,
        { exact xs, },
        { dsimp,
          exact h, }},
      { right,
        exact xt, }}},
end

-- 2ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x,
  split,
  { rintros (⟨xs, nxt⟩ | xt),
    { left,
      exact xs},
    { right,
      exact xt }},
  { by_cases h : x ∈ t,
    { intro _,
      right,
      exact h },
    { rintros (xs | xt),
      { left,
        use [xs, h] },
      { right,
        use xt }}},
end

-- 3ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
begin
  rw ext_iff,
  intro,
  rw iff_def,
  finish,
end

-- 4ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
by finish [ext_iff, iff_def]

-- 5ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
diff_union_self

-- 6ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext,
  simp,
end

-- 7ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
by simp
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Union_con_su_diferencia
imports Main
begin

section ‹1ª demostración: Detallada›

lemma "(s - t) ∪ t = s ∪ t"
proof (rule equalityI)
  show "(s - t) ∪ t ⊆ s ∪ t"
  proof (rule subsetI)
    fix x
    assume "x ∈ (s - t) ∪ t"
    then show "x ∈ s ∪ t"
    proof (rule UnE)
      assume "x ∈ s - t"
      then have "x ∈ s"
        by (simp only: DiffD1)
      then show "x ∈ s ∪ t"
        by (simp only: UnI1)
    next
      assume "x ∈ t"
      then show "x ∈ s ∪ t"
        by (simp only: UnI2)
    qed
  qed
next
  show "s ∪ t ⊆ (s - t) ∪ t"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∪ t"
    then show "x ∈ (s - t) ∪ t"
    proof (rule UnE)
      assume "x ∈ s"
      show "x ∈ (s - t) ∪ t"
      proof (cases ‹x ∈ t›)
        assume "x ∈ t"
        then show "x ∈ (s - t) ∪ t"
          by (simp only: UnI2)
      next
        assume "x ∉ t"
        with ‹x ∈ s› have "x ∈ s - t"
          by (rule DiffI)
        then show "x ∈ (s - t) ∪ t"
          by (simp only: UnI1)
      qed
    next
      assume "x ∈ t"
      then show "x ∈ (s - t) ∪ t"
        by (simp only: UnI2)
    qed
  qed
qed

section ‹2ª demostración: Estructurada›

lemma "(s - t) ∪ t = s ∪ t"
proof
  show "(s - t) ∪ t ⊆ s ∪ t"
  proof
    fix x
    assume "x ∈ (s - t) ∪ t"
    then show "x ∈ s ∪ t"
    proof
      assume "x ∈ s - t"
      then have "x ∈ s"
        by simp
      then show "x ∈ s ∪ t"
        by simp
    next
      assume "x ∈ t"
      then show "x ∈ s ∪ t"
        by simp
    qed
  qed
next
  show "s ∪ t ⊆ (s - t) ∪ t"
  proof
    fix x
    assume "x ∈ s ∪ t"
    then show "x ∈ (s - t) ∪ t"
    proof
      assume "x ∈ s"
      show "x ∈ (s - t) ∪ t"
      proof
        assume "x ∉ t"
        with ‹x ∈ s› show "x ∈ s - t"
          by simp
      qed
    next
      assume "x ∈ t"
      then show "x ∈ (s - t) ∪ t"
        by simp
    qed
  qed
qed

section ‹3ª demostración: Con lema›

lemma "(s - t) ∪ t = s ∪ t"
by (fact Un_Diff_cancel2)

section ‹4ª demostración: Automática›

lemma "(s - t) ∪ t = s ∪ t"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
