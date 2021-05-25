---
Título: Unión con su intersección
Autor:  José A. Alonso
---

Demostrar que

> s ∪ (s ∩ t) = s

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

example : s ∪ (s ∩ t) = s :=
sorry
</pre>

<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

-- 1ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  split,
  { intro hx,
    cases hx with xs xst,
    { exact xs, },
    { exact xst.1, }},
  { intro xs,
    left,
    exact xs, },
end

-- 2ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  exact ⟨λ hx, or.dcases_on hx id and.left,
         λ xs, or.inl xs⟩,
end

-- 3ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  split,
  { rintros (xs | ⟨xs, xt⟩);
    exact xs },
  { intro xs,
    left,
    exact xs },
end

-- 4ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
sup_inf_self
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Union_con_su_interseccion
imports Main
begin

(* 1ª demostración *)
lemma "s ∪ (s ∩ t) = s"
proof (rule equalityI)
  show "s ∪ (s ∩ t) ⊆ s"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∪ (s ∩ t)"
    then show "x ∈ s"
    proof
      assume "x ∈ s"
      then show "x ∈ s"
        by this
    next
      assume "x ∈ s ∩ t"
      then show "x ∈ s"
        by (simp only: IntD1)
    qed
  qed
next
  show "s ⊆ s ∪ (s ∩ t)"
  proof (rule subsetI)
    fix x
    assume "x ∈ s"
    then show "x ∈ s ∪ (s ∩ t)"
      by (simp only: UnI1)
  qed
qed

(* 2ª demostración *)
lemma "s ∪ (s ∩ t) = s"
proof
  show "s ∪ s ∩ t ⊆ s"
  proof
    fix x
    assume "x ∈ s ∪ (s ∩ t)"
    then show "x ∈ s"
    proof
      assume "x ∈ s"
      then show "x ∈ s"
        by this
    next
      assume "x ∈ s ∩ t"
      then show "x ∈ s"
        by simp
    qed
  qed
next
  show "s ⊆ s ∪ (s ∩ t)"
  proof
    fix x
    assume "x ∈ s"
    then show "x ∈ s ∪ (s ∩ t)"
      by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∪ (s ∩ t) = s"
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
