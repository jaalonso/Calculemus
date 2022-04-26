---
Título: Diferencia de diferencia de conjuntos
Autor:  José A. Alonso
---

Demostrar que `(s \ t) \ u ⊆ s \ (t ∪ u)`

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
sorry
</pre>

## Soluciones con Lean

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x hx,
  cases hx with hxst hxnu,
  cases hxst with hxs hxnt,
  split,
  { exact hxs },
  { dsimp,
    by_contradiction hxtu,
    cases hxtu with hxt hxu,
    { apply hxnt,
      exact hxt, },
    { apply hxnu,
      exact hxu, }},
end

-- 2ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨hxs, hxnt⟩, hxnu⟩,
  split,
  { exact hxs },
  { by_contradiction hxtu,
    cases hxtu with hxt hxu,
    { exact hxnt hxt, },
    { exact hxnu hxu, }},
end

-- 3ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu),
  { contradiction, },
  { contradiction, },
end

-- 4ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction,
end

-- 5ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  simp at *,
  finish,
end

-- 6ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  finish,
end

-- 7ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by rw diff_diff

-- 8ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by tidy
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Demostrando-con-Lean/blob/main/src/Diferencia_de_diferencia_de_conjuntos.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Demostrando-con-Lean/main/src/Diferencia_de_diferencia_de_conjuntos.lean).

La construcción de las demostraciones se muestra en el siguiente vídeo



## Soluciones con Isabelle/HOL

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
