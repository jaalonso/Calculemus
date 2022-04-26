---
Título: Intersección con su unión
Autor:  José A. Alonso
---

Demostrar que `s ∩ (s ∪ t) = s`

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t : set α

example : s ∩ (s ∪ t) = s :=
sorry
</pre>

<!-- more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
import tactic
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
begin
  apply subset_antisymm,
  { rintros x ⟨hxs,-⟩,
    exact hxs, },
  { intros x hxs,
    exact ⟨hxs, or.inl hxs⟩, },
end

-- 8ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
-- by suggest
inf_sup_self

-- 9ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
-- by hint
by finish
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Razonando-con-Lean/blob/main/src/Interseccion_con_su_union.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Razonando-con-Lean/main/src/Interseccion_con_su_union.lean).

La construcción de las demostraciones se muestra en el siguiente vídeo


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
