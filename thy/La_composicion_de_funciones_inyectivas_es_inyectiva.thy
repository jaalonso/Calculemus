(* La_composicion_de_funciones_inyectivas_es_inyectiva.thy
-- La composición de funciones inyectivas es inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 14 de agosto de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la composición de dos funciones inyectivas es una
-- función inyectiva.
-- ------------------------------------------------------------------ *)

theory La_composicion_de_funciones_inyectivas_es_inyectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f \<circ> g)"
proof (rule injI)
  fix x y
  assume "(f \<circ> g) x = (f \<circ> g) y"
  then have "f (g x) = f (g y)"
    by (simp only: o_apply)
  then have "g x = g y"
    using \<open>inj f\<close> by (simp only: injD)
  then show "x = y" 
    using \<open>inj g\<close> by (simp only: injD)
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f \<circ> g)"
using assms
by (simp add: inj_def)

(* 3\<ordfeminine> demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f \<circ> g)"
using assms
by (rule inj_compose)

end