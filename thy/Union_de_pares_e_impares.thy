(* Union_de_pares_e_impares.thy
   Unión de pares e impares
   José A. Alonso Jiménez
   Sevilla, 31 de mayo de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
  Los conjuntos de los números naturales, de los pares y de los impares
  se definen por
     def naturales : set \<nat> := {n | true}
     def pares     : set \<nat> := {n | even n}
     def impares   : set \<nat> := {n | \<not> even n}

  Demostrar que
     pares \<union> impares = naturales
  ---------------------------------------------------------------------\<close>

theory Union_de_pares_e_impares
imports Main
begin

definition naturales :: "nat set" where  
  "naturales = {n\<in>\<nat> . True}"

definition pares :: "nat set" where  
  "pares = {n\<in>\<nat> . even n}"

definition impares :: "nat set" where  
  "impares = {n\<in>\<nat> . \<not> even n}"

section \<open>1\<ordfeminine> demostración\<close>

lemma "pares \<union> impares = naturales"
proof -
  have "\<forall> n \<in> \<nat> . even n \<or> \<not> even n \<longleftrightarrow> True"
    by simp
  then have "{n \<in> \<nat>. even n} \<union> {n \<in> \<nat>. \<not> even n} = {n \<in> \<nat>. True}"
    by auto
  then show "pares \<union> impares = naturales"
    by (simp add: naturales_def pares_def impares_def)
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma "pares \<union> impares = naturales"
  unfolding naturales_def pares_def impares_def
  by auto

end
