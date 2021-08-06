(* La_composicion_de_funciones_suprayectivas_es_suprayectiva.thy
-- La composición de funciones suprayectivas es suprayectiva.
-- José A. Alonso Jiménez
-- Sevilla, 15 de agosto de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la composición de dos funciones suprayectivas es una
-- función suprayectiva.
-- ------------------------------------------------------------------ *)

theory La_composicion_de_funciones_suprayectivas_es_suprayectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "surj (f :: 'a \<Rightarrow> 'b)"
          "surj (g :: 'b \<Rightarrow> 'c)"
  shows   "surj (g \<circ> f)"
proof (unfold surj_def; intro allI)
  fix z
  obtain y where hy : "g y = z"
    using \<open>surj g\<close> by (metis surjD)
  obtain x where hx : "f x = y"
    using \<open>surj f\<close> by (metis surjD)
  have "(g \<circ> f) x = g (f x)"
    by (simp only: o_apply)
  also have "\<dots> = g y"
    by (simp only: \<open>f x = y\<close>)
  also have "\<dots> = z"
    by (simp only: \<open>g y = z\<close>)
  finally have "(g \<circ> f) x = z"
    by this
  then have "z = (g \<circ> f) x"
    by (rule sym)
  then show "\<exists>x. z = (g \<circ> f) x"
    by (rule exI)
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "surj f"
          "surj g"
  shows   "surj (g \<circ> f)"
using assms image_comp [of g f UNIV]
by (simp only:)

(* 3\<ordfeminine> demostración *)
lemma
  assumes "surj f"
          "surj g"
  shows   "surj (g \<circ> f)"
using assms
by (rule comp_surj)

end
