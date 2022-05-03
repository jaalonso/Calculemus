---
Título: Propiedad semidistributiva de la intersección sobre la unión
Autor:  José A. Alonso
---

Demostrar que `s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)`.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
sorry
</pre>

## 1. Soluciones con Lean

<pre lang="lean">
import data.set.basic
import tactic

open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  cases hx with hxs hxtu,
  cases hxtu with hxt hxu,
  { left,
    split,
    { exact hxs, },
    { exact hxt, }},
  { right,
    split,
    { exact hxs, },
    { exact hxu, }},
end

-- 2ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨hxs, hxt | hxu⟩,
  { left,
    exact ⟨hxs, hxt⟩, },
  { right,
    exact ⟨hxs, hxu⟩, },
end

-- 3ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨hxs, hxt | hxu⟩,
  { exact or.inl ⟨hxs, hxt⟩, },
  { exact or.inr ⟨hxs, hxu⟩, },
end

-- 4ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  by finish,
end

-- 5ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by rw inter_union_distrib_left
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Razonando-con-Lean/blob/main/src/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Razonando-con-Lean/main/src/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.lean).

La construcción de las demostraciones se muestra en el siguiente vídeo

<iframe width="560" height="315" src="https://www.youtube.com/embed/DRKAjEeeM_8" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

## 2. Soluciones con Isabelle/HOL

<pre lang="isar">
theory Propiedad_semidistributiva_de_la_interseccion_sobre_la_union
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by (simp only: IntD1)
  have xtu: "x ∈ t ∪ u"
    using hx by (simp only: IntD2)
  then have "x ∈ t ∨ x ∈ u"
    by (simp only: Un_iff)
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule disjE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI1)
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI2)
  qed
qed

(* 2ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by simp
  have xtu: "x ∈ t ∪ u"
    using hx by simp
  then have "x ∈ t ∨ x ∈ u"
    by simp
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by (simp only: IntD1)
  have xtu: "x ∈ t ∪ u"
    using hx by (simp only: IntD2)
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule UnE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI1)
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI2)
  qed
qed

(* 4ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by simp
  have xtu: "x ∈ t ∪ u"
    using hx by simp
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule UnE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  qed
qed

(* 5ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
by (simp only: Int_Un_distrib)

(* 6ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
by auto

end
</pre>
