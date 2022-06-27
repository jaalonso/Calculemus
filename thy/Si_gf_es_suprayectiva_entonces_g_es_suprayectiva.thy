(* Si_gf_es_suprayectiva_entonces_g_es_suprayectiva.thy
-- Si gf es suprayectiva, entonces g es suprayectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-junio-2022
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si g\<sqdot>f es suprayectiva, entonces g es suprayectiva
-- ------------------------------------------------------------------ *)

theory Si_gf_es_suprayectiva_entonces_g_es_suprayectiva
imports Main
begin 

lemma
  fixes   f :: "'a \<Rightarrow> 'b" and 
          g :: "'b \<Rightarrow> 'c"
  assumes "surj (g \<circ> f)"
  shows   "surj g"
using assms by fastforce

end