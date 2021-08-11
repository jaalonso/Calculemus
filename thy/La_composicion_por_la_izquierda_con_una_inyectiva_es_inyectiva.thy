(* La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.thy
-- La composición por la izquierda con una inyectiva es una operación inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 20 de agosto de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean f₁ y f₂ funciones de X en Y y g una función de X en Y. Demostrar
-- que si g es inyectiva y g \<circ> f₁ = g \<circ> f₂, entonces f₁ = f₂.
-- ------------------------------------------------------------------ *)

theory La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
proof (rule ext)
  fix x
  have "(g \<circ> f1) x = (g \<circ> f2) x"
    using \<open>g \<circ> f1 = g \<circ> f2\<close> by (rule fun_cong)
  then have "g (f1 x) = g (f2 x)"
    by (simp only: o_apply)
  then show "f1 x = f2 x" 
    using \<open>inj g\<close> by (simp only: injD)
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
proof 
  fix x
  have "(g \<circ> f1) x = (g \<circ> f2) x"
    using \<open>g \<circ> f1 = g \<circ> f2\<close> by simp
  then have "g (f1 x) = g (f2 x)"
    by simp 
  then show "f1 x = f2 x" 
    using \<open>inj g\<close> by (simp only: injD)
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
using assms
by (metis fun.inj_map_strong inj_eq)

end
