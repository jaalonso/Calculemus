(* Una_funcion_tiene_inversa_por_la_derecha_si_y_solo_si_es_suprayectiva.thy
-- Una función tiene inversa por la derecha si y solo si es suprayectiva
-- José A. Alonso Jiménez
-- Sevilla, 7 de agosto de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir que f tenga inversa por la
-- derecha por
--    definition tiene_inversa_dcha :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
--      "tiene_inversa_dcha f \<longleftrightarrow> (\<exists>g. \<forall>y. f (g y) = y)"
--
-- Demostrar que la función f tiene inversa por la derecha si y solo si
-- es suprayectiva.
-- ------------------------------------------------------------------ *)

theory Una_funcion_tiene_inversa_por_la_derecha_si_y_solo_si_es_suprayectiva
imports Main
begin

definition tiene_inversa_dcha :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa_dcha f \<longleftrightarrow> (\<exists>g. \<forall>y. f (g y) = y)"

(* 1\<ordfeminine> demostración *)
lemma
  "tiene_inversa_dcha f \<longleftrightarrow> surj f"
proof (rule iffI)
  assume hf : "tiene_inversa_dcha f"
  show "surj f" 
  proof (unfold surj_def; intro allI)
    fix y
    obtain g where "\<forall>y. f (g y) = y"
      using hf tiene_inversa_dcha_def by auto
    then have "f (g y) = y"
      by (rule allE)
    then have "y = f (g y)"
      by (rule sym)
    then show "\<exists>x. y = f x"
      by (rule exI)
  qed
next
  assume hf : "surj f"
  show "tiene_inversa_dcha f" 
  proof (unfold tiene_inversa_dcha_def)
    let ?g = "\<lambda>y. SOME x. f x = y"
    have "\<forall>y. f (?g y) = y"
    proof (rule allI)
      fix y
      have "\<exists>x. f x = y"
        by (metis hf surjD)
      then show "f (?g y) = y"
        by (rule someI_ex)
    qed
  then show "\<exists>g. \<forall>y. f (g y) = y" 
    by auto
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma
  "tiene_inversa_dcha f \<longleftrightarrow> surj f"
proof (rule iffI)
  assume "tiene_inversa_dcha f"
  then show "surj f" 
    using tiene_inversa_dcha_def surj_def
    by metis
next
  assume "surj f"
  then show "tiene_inversa_dcha f" 
    by (metis surjD tiene_inversa_dcha_def)
qed

end
