---
Título: Las clases de equivalencia de elementos no relacionados son disjuntas
Autor:  José A. Alonso
---

Demostrar que las clases de equivalencia de elementos no relacionados son disjuntas.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

example
  (h : equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- 1ª demostración
example
  (h : equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
begin
  rcases h with ⟨hr, hs, ht⟩,
  by_contradiction h1,
  apply hxy,
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y,
    { contrapose h1,
      intro h1a,
      apply h1a,
      push_neg at h1,
      exact set.eq_empty_iff_forall_not_mem.mpr h1, },
  rcases h2 with ⟨z, hxz, hyz⟩,
  replace hxz : R x z := hxz,
  replace hyz : R y z := hyz,
  have hzy : R z y := hs hyz,
  exact ht hxz hzy,
end

-- 2ª demostración
example
  (h : equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
begin
  rcases h with ⟨hr, hs, ht⟩,
  by_contradiction h1,
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y,
    { by finish [set.eq_empty_iff_forall_not_mem]},
  apply hxy,
  rcases h2 with ⟨z, hxz, hyz⟩,
  exact ht hxz (hs hyz),
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas
imports Main
begin

definition clase :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a set"
  where "clase R x = {y. R x y}"

(* 1ª demostración *)
lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
proof -
  have "∀z. z ∈ clase R x ⟶ z ∉ clase R y"
  proof (intro allI impI)
    fix z
    assume "z ∈ clase R x"
    then have "R x z"
      using clase_def by (metis CollectD)
    show "z ∉ clase R y"
    proof (rule notI)
      assume "z ∈ clase R y"
      then have "R y z"
        using clase_def by (metis CollectD)
      then have "R z y"
        using assms(1) by (simp only: equivp_symp)
      with ‹R x z› have "R x y"
        using assms(1) by (simp only: equivp_transp)
      with ‹¬R x y› show False
        by (rule notE)
    qed
  qed
  then show "clase R x ∩ clase R y = {}"
    by (simp only: disjoint_iff)
qed

(* 2ª demostración *)
lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
proof -
  have "∀z. z ∈ clase R x ⟶ z ∉ clase R y"
  proof (intro allI impI)
    fix z
    assume "z ∈ clase R x"
    then have "R x z"
      using clase_def by fastforce
    show "z ∉ clase R y"
    proof (rule notI)
      assume "z ∈ clase R y"
      then have "R y z"
        using clase_def by fastforce
      then have "R z y"
        using assms(1) by (simp only: equivp_symp)
      with ‹R x z› have "R x y"
        using assms(1) by (simp only: equivp_transp)
      with ‹¬R x y› show False
        by simp
    qed
  qed
  then show "clase R x ∩ clase R y = {}"
    by (simp only: disjoint_iff)
qed

(* 3ª demostración *)
lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
  using assms
  by (metis clase_def
            CollectD
            equivp_symp
            equivp_transp
            disjoint_iff)

(* 4ª demostración *)
lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
  using assms
  by (metis equivp_def
            clase_def
            CollectD
            disjoint_iff_not_equal)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
