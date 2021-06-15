(* Intersecion_con_la_imagen_inversa.thy
-- Intersección con la imagen inversa
-- José A. Alonso Jiménez
-- Sevilla, 21 de junio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    s \<inter> f -'  v \<subseteq> f -` (f ` s \<inter> v)
-- ------------------------------------------------------------------ *)

theory Union_con_la_imagen_inversa
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "s \<inter> f -`  v \<subseteq> f -` (f ` s \<inter> v)"
proof (rule subsetI)
  fix x
  assume "x \<in> s \<inter> f -`  v"
  have "f x \<in> f ` s"
  proof -
    have "x \<in> s"
      using \<open>x \<in> s \<inter> f -`  v\<close> by (rule IntD1)
    then show "f x \<in> f ` s"
      by (rule imageI)
  qed
  moreover
  have "f x \<in> v"
  proof -
    have "x \<in> f -`  v"
      using \<open>x \<in> s \<inter> f -`  v\<close> by (rule IntD2)
    then show "f x \<in> v"
      by (rule vimageD)
  qed
  ultimately have "f x \<in> f ` s \<inter> v"
    by (rule IntI)
  then show "x \<in> f -` (f ` s \<inter> v)"
    by (rule vimageI2)
qed

(* 2\<ordfeminine> demostración *)

lemma "s \<inter> f -`  v \<subseteq> f -` (f ` s \<inter> v)"
proof (rule subsetI)
  fix x
  assume "x \<in> s \<inter> f -`  v"
  have "f x \<in> f ` s"
  proof -
    have "x \<in> s" using \<open>x \<in> s \<inter> f -`  v\<close> by simp
    then show "f x \<in> f ` s" by simp
  qed
  moreover
  have "f x \<in> v"
  proof -
    have "x \<in> f -`  v" using \<open>x \<in> s \<inter> f -`  v\<close> by simp
    then show "f x \<in> v" by simp
  qed
  ultimately have "f x \<in> f ` s \<inter> v" by simp
  then show "x \<in> f -` (f ` s \<inter> v)" by simp
qed

(* 3\<ordfeminine> demostración *)

lemma "s \<inter> f -`  v \<subseteq> f -` (f ` s \<inter> v)"
  by auto

end
