---
Título: Intersección con su unión
Autor:  José A. Alonso
---

Demostrar que

> s ∩ (s ∪ t) = s

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

example : s ∩ (s ∪ t) = s :=
sorry
</pre>

**Notas**

* En [este enlace](https://bit.ly/3vhCL7T) se puede escribir las soluciones en Lean.
* A continuación se muestran algunas soluciones (que se pueden probar en [este enlace](https://bit.ly/3uhrUtp)).
* En los comentarios se pueden publicar otras soluciones, en Lean o en otros sistemas de razonamiento.
  + Para publicar las demostraciones en Lean se deben de escribir entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
  + Para publicar las demostraciones en Isabelle/HOL se deben de escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

-- 1ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    dsimp at h,
    exact h.1, },
  { intro xs,
    dsimp,
    split,
    { exact xs, },
    { left,
      exact xs, }},
end

-- 2ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    exact h.1, },
  { intro xs,
    split,
    { exact xs, },
    { left,
      exact xs, }},
end

-- 3ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    exact h.1, },
  { intro xs,
    split,
    { exact xs, },
    { exact (or.inl xs), }},
end

-- 4ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨λ h, h.1,
         λ xs, ⟨xs, or.inl xs⟩⟩,
end

-- 5ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨and.left,
         λ xs, ⟨xs, or.inl xs⟩⟩,
end

-- 6ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { rintros ⟨xs, _⟩,
    exact xs },
  { intro xs,
    use xs,
    left,
    exact xs },
end

-- 7ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
inf_sup_self
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Interseccion_con_su_union
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ (s ∪ t) = s"
proof (rule  equalityI)
  show "s ∩ (s ∪ t) ⊆ s"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∩ (s ∪ t)"
    then show "x ∈ s"
      by (simp only: IntD1)
  qed
next
  show "s ⊆ s ∩ (s ∪ t)"
  proof (rule subsetI)
    fix x
    assume "x ∈ s"
    then have "x ∈ s ∪ t"
      by (simp only: UnI1)
    with ‹x ∈ s› show "x ∈ s ∩ (s ∪ t)"
      by (rule IntI)
  qed
qed

(* 2ª demostración *)
lemma "s ∩ (s ∪ t) = s"
proof
  show "s ∩ (s ∪ t) ⊆ s"
  proof
    fix x
    assume "x ∈ s ∩ (s ∪ t)"
    then show "x ∈ s"
      by simp
  qed
next
  show "s ⊆ s ∩ (s ∪ t)"
  proof
    fix x
    assume "x ∈ s"
    then have "x ∈ s ∪ t"
      by simp
    then show "x ∈ s ∩ (s ∪ t)"
      using ‹x ∈ s› by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∩ (s ∪ t) = s"
by (fact Un_Int_eq)

(* 4ª demostración *)
lemma "s ∩ (s ∪ t) = s"
by auto
</pre>
