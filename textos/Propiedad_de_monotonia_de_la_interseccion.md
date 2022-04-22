---
Título: Propiedad de monotonía de la intersección.
Autor:  José A. Alonso
---

Demostrar que la intersección es monótona por la izquierda; es decir, si `s ⊆ t`, entonces `s ∩ u ⊆ t ∩ u`.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
sorry
</pre>

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
import tactic

open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw subset_def,
  rw inter_def,
  rw inter_def,
  dsimp,
  intros x h1,
  cases h1 with xs xu,
  split,
  { rw subset_def at h,
    apply h,
    exact xs, },
  { exact xu, },
end

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  dsimp,
  rintros x ⟨xs, xu⟩,
  rw subset_def at h,
  exact ⟨h x xs, xu⟩,
end

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, inter_def, inter_def],
  rintros x ⟨xs, xu⟩,
  rw subset_def at h,
  exact ⟨h _ xs, xu⟩,
end

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩,
end

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rintros x ⟨xs, xu⟩,
  exact ⟨h xs, xu⟩,
end

-- 6ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
-- by library_search
inter_subset_inter_left u h

-- 7ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by tidy
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Demostrando-con-Lean/blob/main/src/Propiedad_de_monotonia_de_la_interseccion.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Demostrando-con-Lean/main/src/Propiedad_de_monotonia_de_la_interseccion.lean).

La construcción de las demostraciones se muestra en el siguiente vídeo

<iframe width="560" height="315" src="https://www.youtube.com/embed/W2_gMDHRehg" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Propiedad_de_monotonia_de_la_interseccion
imports Main
begin

(* 1ª solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
proof  (rule subsetI)
  fix x
  assume hx: "x ∈ s ∩ u"
  have xs: "x ∈ s"
    using hx
    by (simp only: IntD1)
  then have xt: "x ∈ t"
    using assms
    by (simp only: subset_eq)
  have xu: "x ∈ u"
    using hx
    by (simp only: IntD2)
  show "x ∈ t ∩ u"
    using xt xu
    by (simp only: Int_iff)
qed

(* 2 solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
proof
  fix x
  assume hx: "x ∈ s ∩ u"
  have xs: "x ∈ s"
    using hx
    by simp
  then have xt: "x ∈ t"
    using assms
    by auto
  have xu: "x ∈ u"
    using hx
    by simp
  show "x ∈ t ∩ u"
    using xt xu
    by simp
qed

(* 3ª solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
using assms
by auto

(* 4ª solución *)
lemma
  "s ⊆ t ⟹ s ∩ u ⊆ t ∩ u"
by auto

end
</pre>
