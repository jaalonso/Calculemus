(* Propiedad_cancelativa_del_producto_de_numeros_naturales.thy
-- Propiedad cancelativa del producto de números naturales
-- José A. Alonso Jiménez
-- Sevilla, 28 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean k, m, n números naturales. Demostrar que
--    k * m = k * n \<leftrightarrow> m = n \<or> k = 0
-- ------------------------------------------------------------------ *)

theory Propiedad_cancelativa_del_producto_de_numeros_naturales
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0"
proof -
  have "k \<noteq> 0 \<Longrightarrow> k * m = k * n \<Longrightarrow> m = n"
  proof (induct n arbitrary: m)
    fix m
    assume "k \<noteq> 0" and "k * m = k * 0"
    show "m = 0" 
      using \<open>k * m = k * 0\<close>
      by (simp only: mult_left_cancel[OF \<open>k \<noteq> 0\<close>])
  next
    fix n m
    assume HI : "\<And>m. \<lbrakk>k \<noteq> 0; k * m = k * n\<rbrakk> \<Longrightarrow> m = n"
       and hk : "k \<noteq> 0"
       and "k * m = k * Suc n"
    then show "m = Suc n"
    proof (cases m)
      assume "m = 0"
      then show "m = Suc n"
        using \<open>k * m = k * Suc n\<close> 
        by (simp only: mult_left_cancel[OF \<open>k \<noteq> 0\<close>])
    next
      fix m'
      assume "m = Suc m'"
      then have "k * Suc m' = k * Suc n"
        using \<open>k * m = k * Suc n\<close> by (rule subst)
      then have "k * m' + k = k * n + k"
        by (simp only: mult_Suc_right)
      then have "k * m' = k * n"
        by (simp only: add_right_imp_eq)
      then have "m' = n"
        by (simp only: HI[OF hk]) 
      then show "m = Suc n"
        by (simp only: \<open>m = Suc m'\<close>) 
    qed
  qed
  then show "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0" 
    by auto
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0"
proof -
  have "k \<noteq> 0 \<Longrightarrow> k * m = k * n \<Longrightarrow> m = n"
  proof (induct n arbitrary: m)
    fix m
    assume "k \<noteq> 0" and "k * m = k * 0"
    then show "m = 0" by simp
  next
    fix n m
    assume "\<And>m. \<lbrakk>k \<noteq> 0; k * m = k * n\<rbrakk> \<Longrightarrow> m = n"
       and "k \<noteq> 0"
       and "k * m = k * Suc n"
    then show "m = Suc n"
    proof (cases m)
      assume "m = 0"
      then show "m = Suc n"
        using \<open>k * m = k * Suc n\<close> \<open>k \<noteq> 0\<close> by auto
    next
      fix m'
      assume "m = Suc m'"
      then show "m = Suc n"
        using \<open>k * m = k * Suc n\<close> \<open>k \<noteq> 0\<close> by force
    qed
  qed
  then show "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0" by auto
qed

(* 3\<ordfeminine> demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0"
proof -
  have "k \<noteq> 0 \<Longrightarrow> k * m = k * n \<Longrightarrow> m = n"
  proof (induct n arbitrary: m)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    then show ?case 
    proof (cases m)
      case 0
      then show ?thesis 
        using Suc.prems by auto
    next
      case (Suc nat)
      then show ?thesis 
        using Suc.prems by auto
    qed
  qed
  then show ?thesis
    by auto
qed

(* 4\<ordfeminine> demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0"
proof -
  have "k \<noteq> 0 \<Longrightarrow> k * m = k * n \<Longrightarrow> m = n"
  proof (induct n arbitrary: m)
    case 0
    then show "m = 0" by simp
  next
    case (Suc n)
    then show "m = Suc n"
      by (cases m) (simp_all add: eq_commute [of 0])
  qed
  then show ?thesis by auto
qed

(* 5\<ordfeminine> demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0"
by (simp only: mult_cancel1)

(* 6\<ordfeminine> demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0"
by simp

end
