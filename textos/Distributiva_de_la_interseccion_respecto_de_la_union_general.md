---
Título: Distributiva de la intersección respecto de la unión general
Autor:  José A. Alonso
---

Demostrar que `s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)`

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import data.set.lattice
import tactic

open set

variable {α : Type}
variable s : set α
variable A : ℕ → set α

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
sorry
</pre>

<h4>Soluciones</h4>
<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
import data.set.lattice
import tactic

open set

variable {α : Type}
variable s : set α
variable A : ℕ → set α

-- 1ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  split,
  { intro h,
    rw mem_Union,
    cases h with xs xUAi,
    rw mem_Union at xUAi,
    cases xUAi with i xAi,
    use i,
    split,
    { exact xAi, },
    { exact xs, }},
  { intro h,
    rw mem_Union at h,
    cases h with i hi,
    cases hi with xAi xs,
    split,
    { exact xs, },
    { rw mem_Union,
      use i,
      exact xAi, }},
end

-- 2ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp,
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨⟨i, xAi⟩, xs⟩, },
  { rintros ⟨⟨i, xAi⟩, xs⟩,
    exact ⟨xs, ⟨i, xAi⟩⟩ },
end

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  finish,
end

-- 4ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by ext; finish

-- 5ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by finish [ext_iff]

-- 6ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by tidy
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Razonando-con-Lean/blob/main/src/Distributiva_de_la_interseccion_respecto_de_la_union_general.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Razonando-con-Lean/main/src/Distributiva_de_la_interseccion_respecto_de_la_union_general.lean).

La construcción de las demostraciones se muestra en el siguiente vídeo

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Distributiva_de_la_interseccion_respecto_de_la_union_general
imports Main
begin

section ‹1ª demostración›

lemma "s ∩ (⋃ i ∈ I. A i) = (⋃ i ∈ I. (A i ∩ s))"
proof (rule equalityI)
  show "s ∩ (⋃ i ∈ I. A i) ⊆ (⋃ i ∈ I. (A i ∩ s))"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∩ (⋃ i ∈ I. A i)"
    then have "x ∈ s"
      by (simp only: IntD1)
    have "x ∈ (⋃ i ∈ I. A i)"
      using ‹x ∈ s ∩ (⋃ i ∈ I. A i)› by (simp only: IntD2)
    then show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "x ∈ A i"
      then have "x ∈ A i ∩ s"
        using ‹x ∈ s› by (rule IntI)
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
        by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. (A i ∩ s)) ⊆ s ∩ (⋃ i ∈ I. A i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (⋃ i ∈ I. A i ∩ s)"
    then show "x ∈ s ∩ (⋃ i ∈ I. A i)"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "x ∈ A i ∩ s"
      then have "x ∈ A i"
        by (rule IntD1)
      have "x ∈ s"
        using ‹x ∈ A i ∩ s› by (rule IntD2)
      moreover
      have "x ∈ (⋃ i ∈ I. A i)"
        using ‹i ∈ I› ‹x ∈ A i› by (rule UN_I)
      ultimately show "x ∈ s ∩ (⋃ i ∈ I. A i)"
        by (rule IntI)
    qed
  qed
qed

section ‹2ª demostración›

lemma "s ∩ (⋃ i ∈ I. A i) = (⋃ i ∈ I. (A i ∩ s))"
proof
  show "s ∩ (⋃ i ∈ I. A i) ⊆ (⋃ i ∈ I. (A i ∩ s))"
  proof
    fix x
    assume "x ∈ s ∩ (⋃ i ∈ I. A i)"
    then have "x ∈ s"
      by simp
    have "x ∈ (⋃ i ∈ I. A i)"
      using ‹x ∈ s ∩ (⋃ i ∈ I. A i)› by simp
    then show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
    proof
      fix i
      assume "i ∈ I"
      assume "x ∈ A i"
      then have "x ∈ A i ∩ s"
        using ‹x ∈ s› by simp
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
        by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. (A i ∩ s)) ⊆ s ∩ (⋃ i ∈ I. A i)"
  proof
    fix x
    assume "x ∈ (⋃ i ∈ I. A i ∩ s)"
    then show "x ∈ s ∩ (⋃ i ∈ I. A i)"
    proof
      fix i
      assume "i ∈ I"
      assume "x ∈ A i ∩ s"
      then have "x ∈ A i"
        by simp
      have "x ∈ s"
        using ‹x ∈ A i ∩ s› by simp
      moreover
      have "x ∈ (⋃ i ∈ I. A i)"
        using ‹i ∈ I› ‹x ∈ A i› by (rule UN_I)
      ultimately show "x ∈ s ∩ (⋃ i ∈ I. A i)"
        by simp
    qed
  qed
qed

section ‹3ª demostración›

lemma "s ∩ (⋃ i ∈ I. A i) = (⋃ i ∈ I. (A i ∩ s))"
  by auto

end
</pre>
