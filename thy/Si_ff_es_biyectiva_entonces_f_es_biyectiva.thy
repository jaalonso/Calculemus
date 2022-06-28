(* Si_ff_es_biyectiva_entonces_f_es_biyectiva.thy
-- Si f\<sqdot>f es biyectiva entonces f es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-junio-2022
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si f\<sqdot>f es biyectiva, entonces f es biyectiva.
-- ------------------------------------------------------------------ *)

theory Si_ff_es_biyectiva_entonces_f_es_biyectiva
imports Main
begin 

lemma
  assumes "bij (f \<circ> f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f" 
  proof -
    have h1 : "inj (f \<circ> f)"
      using assms by (simp only: bij_is_inj)
    then show "inj f"
      by (simp only: inj_on_imageI2)
  qed 
next
  show "surj f"
  proof -
    have h2 : "surj (f \<circ> f)"
      using assms by (simp only: bij_is_surj)
    then show "surj f"
      by auto
  qed
qed

end
