(* Union_con_interseccion_general.thy
   Unión con intersección general
   José A. Alonso Jiménez
   Sevilla, 4 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que
      s \<union> (\<Inter> i. A i) = (\<Inter> i. A i \<union> s)
  ---------------------------------------------------------------------\<close>

theory Union_con_interseccion_general
imports Main
begin

section \<open>1\<ordfeminine> demostración\<close>

lemma "s \<union> (\<Inter> i \<in> I. A i) = (\<Inter> i \<in> I. A i \<union> s)"
proof (rule equalityI)
  show "s \<union> (\<Inter> i \<in> I. A i) \<subseteq> (\<Inter> i \<in> I. A i \<union> s)"
  proof (rule subsetI)
    fix x
    assume "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    then show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    proof (rule UnE)
      assume "x \<in> s"
      show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
      proof (rule INT_I)
        fix i
        assume "i \<in> I"
        show "x \<in> A i \<union> s"
          using \<open>x \<in> s\<close> by (rule UnI2)
      qed
    next
      assume h1 : "x \<in> (\<Inter> i \<in> I. A i)"
      show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
      proof (rule INT_I)
        fix i
        assume "i \<in> I"
        with h1 have "x \<in> A i"
          by (rule INT_D)
        then show "x \<in> A i \<union> s"
          by (rule UnI1)
      qed
    qed
  qed
next
  show "(\<Inter> i \<in> I. A i \<union> s) \<subseteq> s \<union> (\<Inter> i \<in> I. A i)"
  proof (rule subsetI)
    fix x
    assume h2 : "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    proof (cases "x \<in> s")
      assume "x \<in> s"
      then show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
        by (rule UnI1)
    next
      assume "x \<notin> s"
      have "x \<in> (\<Inter> i \<in> I. A i)"
      proof (rule INT_I)
        fix i
        assume "i \<in> I"
        with h2 have "x \<in> A i \<union> s"
          by (rule INT_D)
        then show "x \<in> A i"
        proof (rule UnE)
          assume "x \<in> A i"
          then show "x \<in> A i"
            by this
        next
          assume "x \<in> s"
          with \<open>x \<notin> s\<close> show "x \<in> A i"
            by (rule notE)
        qed
      qed
      then show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
        by (rule UnI2)
    qed
  qed
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma "s \<union> (\<Inter> i \<in> I. A i) = (\<Inter> i \<in> I. A i \<union> s)"
proof
  show "s \<union> (\<Inter> i \<in> I. A i) \<subseteq> (\<Inter> i \<in> I. A i \<union> s)"
  proof
    fix x
    assume "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    then show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    proof
      assume "x \<in> s"
      show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
      proof
        fix i
        assume "i \<in> I"
        show "x \<in> A i \<union> s"
          using \<open>x \<in> s\<close> by simp
      qed
    next
      assume h1 : "x \<in> (\<Inter> i \<in> I. A i)"
      show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
      proof
        fix i
        assume "i \<in> I"
        with h1 have "x \<in> A i"
          by simp
        then show "x \<in> A i \<union> s"
          by simp
      qed
    qed
  qed
next
  show "(\<Inter> i \<in> I. A i \<union> s) \<subseteq> s \<union> (\<Inter> i \<in> I. A i)"
  proof
    fix x
    assume h2 : "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    proof (cases "x \<in> s")
      assume "x \<in> s"
      then show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
        by simp
    next
      assume "x \<notin> s"
      have "x \<in> (\<Inter> i \<in> I. A i)"
      proof
        fix i
        assume "i \<in> I"
        with h2 have "x \<in> A i \<union> s"
          by (rule INT_D)
        then show "x \<in> A i"
        proof
          assume "x \<in> A i"
          then show "x \<in> A i"
            by this
        next
          assume "x \<in> s"
          with \<open>x \<notin> s\<close> show "x \<in> A i"
            by simp
        qed
      qed
      then show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
        by simp
    qed
  qed
qed

section \<open>3\<ordfeminine> demostración\<close>

lemma "s \<union> (\<Inter> i \<in> I. A i) = (\<Inter> i \<in> I. A i \<union> s)"
proof
  show "s \<union> (\<Inter> i \<in> I. A i) \<subseteq> (\<Inter> i \<in> I. A i \<union> s)"
  proof
    fix x
    assume "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    then show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    proof
      assume "x \<in> s"
      then show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
        by simp
    next
      assume "x \<in> (\<Inter> i \<in> I. A i)"
      then show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
        by simp
    qed
  qed
next
  show "(\<Inter> i \<in> I. A i \<union> s) \<subseteq> s \<union> (\<Inter> i \<in> I. A i)"
  proof
    fix x
    assume h2 : "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    proof (cases "x \<in> s")
      assume "x \<in> s"
      then show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
        by simp
    next
      assume "x \<notin> s"
      then show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
        using h2 by simp
    qed
  qed
qed

section \<open>4\<ordfeminine> demostración\<close>

lemma "s \<union> (\<Inter> i \<in> I. A i) = (\<Inter> i \<in> I. A i \<union> s)"
proof
  show "s \<union> (\<Inter> i \<in> I. A i) \<subseteq> (\<Inter> i \<in> I. A i \<union> s)"
  proof
    fix x
    assume "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    then show "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    proof
      assume "x \<in> s"
      then show ?thesis by simp
    next
      assume "x \<in> (\<Inter> i \<in> I. A i)"
      then show ?thesis by simp
    qed
  qed
next
  show "(\<Inter> i \<in> I. A i \<union> s) \<subseteq> s \<union> (\<Inter> i \<in> I. A i)"
  proof
    fix x
    assume h2 : "x \<in> (\<Inter> i \<in> I. A i \<union> s)"
    show "x \<in> s \<union> (\<Inter> i \<in> I. A i)"
    proof (cases "x \<in> s")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis using h2 by simp
    qed
  qed
qed

section \<open>5\<ordfeminine> demostración\<close>

lemma "s \<union> (\<Inter> i \<in> I. A i) = (\<Inter> i \<in> I. A i \<union> s)"
  by auto


end
