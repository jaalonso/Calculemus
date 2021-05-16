theory TutoList
 
imports Main
 
begin
 
(*
  Definition of a data type "list of 'a", where 'a' is any type.
 
  We hide the list type of HOL/Main as well as the associated notations
  to avoid conflicts with our definition.
*)
  no_notation
        Nil     ("[]")
    and Cons    (infixr "#" 65)
    and append  (infixr "@" 65)
hide_type list
hide_const rev
 
datatype 'a list =
  Nil               ("[]")           (* notation for the empty list *)
| Cons 'a "'a list" (infixr "#" 65)  (* infix right associative notation with priority 65 ( = is 50) *)
 
(*
  Exemples of useful commands to find theorems and print known facts.
 
  Here, we see that "datatype" has generated a lot of theorems about the new type.
  Among them are "list.induct" which allows us to make proofs by structural 
  induction on lists, and "list.simps" which gives the simplification rules
  for list terms.
*)
find_theorems name:"TutoList.list"
thm TutoList.list.induct
(* Note that A ⟹ B ⟹ C ≡ (A and B) ⟹ C, also written ⟦A; B⟧ ⟹ C *)
 
(* Same theorem in a more readable form *)
print_statement TutoList.list.induct
 
(*
  The list.induct theorem has been generated automatically from the
  inductive definition of the "list" type.
  It states that for any predicate P, if P holds for the empty list,
  and if for any item x1 and any list x2, when P holds for x2, 
  it also holds for x1#x2, then P holds for any list.
*)
 
(* Theorems that may be used by the simplifier *)
thm TutoList.list.simps
 
(* About curryfication (named after Haskell Curry)
   In Isabelle, functions are in curryfied form:
     f: A × B → C
        (x, y) ↦ z
   is written as:
     f: A → (B → C)
        x ↦ (λy. z)
   so "f x" is a function which takes the second argument of f to provide the result,
   and "f x y" is read as "(f x) y"
*)

(* Define sum as the function which returns the sum of two integers *)
definition sum:: "int ⇒ int ⇒ int"
where "sum m n = m + n"
 
(* Check that it works as expected *)
value "sum 2 3"
 
(* We can partially apply sum to one argument to define the increment function *)
abbreviation "inc ≡ sum 1"
 
value "inc 41"
 
(* End of the parentheses about curryfication *)
 
(*
  Append a list to the end of another list (concatenation).
  append(l1, l2) is written append l1 l2 (Curryfication)
*)
fun append:: "'a list ⇒ 'a list ⇒ 'a list" (infixr "@" 65)
where
  "[] @ l2 = l2"
| "(x # l1) @ l2 = x # (l1 @ l2)"
 
value "(a # b # c # []) @ (d # e # [])"
 
(* Reverse a list *)
fun rev:: "'a list ⇒ 'a list"
where
  "rev [] = []"
| "rev (x # l) = (rev l) @ (x # [])"
 
(* "value" prints the value of a term. *)
value "rev (a # b # c # [])"
 
(*
  Theorem automatically generated from the definition of function rev,
  that will be used by the simplifier.
*)
thm rev.simps(1)
thm rev.simps(2)
 
(* Standard ML code is generated automatically from our definitions. *)
ML‹
  val frev = @{code rev};    (* the ML function for rev *)
  val fcons = @{code "Cons"};(* the ML function for Cons *)
  val vnil = @{code "Nil"};  (* the ML value for Nil *)
  (* Let's build a list *)
  val l = fcons(1, fcons(2, fcons(3, fcons(4, vnil))));
  (* and reverse it. *)
  frev l;
›
 
(*
  A lemma stating that appending the empty list to a list does nothing.
  This lemma is proved automatically by induction on the list and applying the simplifier
  several times. 'simp' applies the simplifier, '+' means as many times 
  as necessary to prove all goals.
  The "[simp]" modifier says that this lemma can be added to the list 
  of facts used by the simp method to simplify terms.
  One should be careful when annotating lemmas with [simp]: the lemma 
  should really simplify a term!
*)
lemma append_nil[simp]: "l @ [] = l"
by (induction l, simp+)
 
(* A structured proof of the same lemma *)
(*
  Structured proofs are enclosed between "proof" and "qed".
  "proof" can be followed by a method to rewrite the goal. Here, we
  use induction on l. If you do not give a method, Isabelle will
  try to find a suitable one. If you want to work on the raw fact,
  simply put "-" (minus) after "proof". The goal to prove is defined
  as the "?thesis" variable. The proof must end with "show ?thesis by <method>"
  ("thus" is a shortcut for "from this show").
  Induction on l uses the list.induct theorem to split the goal
  in two cases. We can display these cases using the "print_cases"
  command. We have cases Nil and Cons. Writing "case Nil" puts
  us in the context of the Nil case, where the subgoal to prove
  is defined as the "?case" variable. You must write "next" to close
  a case before going to the next one.
  Several patterns can be used in such proofs:
    - from <fact1> have <fact2> by <method>
      This derives <fact2> from <fact1> using <method>. Method "simp"
      uses facts marked as [simp] to rewrite <fact1>. Method "auto"
      uses simp and tries to solve all pending goals. Instead of
      "by <method>", you can use "." when <fact1> and <fact2> are identical.
    - have <fact2> using <fact1> by <method>
      This is identical to "from <fact1> have <fact2> by <method>
    - The last result is known as "this". When you want to derive
      a fact from this, you can write "hence <fact2>" instead of 
      "from this have <fact2>". You can also write "with <fact1> have <fact2>"
      instead of "from <fact1> and this have <fact2>".
    - proving a fact by transitivity:
      have "x1 = x2" by <method>
      also have "... = x3" by <method>
      {* more steps here *}
      also have "... = xn" by <method>
      finally have "x1 = xn" by <method>
    - accumulating facts:
      have <fact1> by <method>
      moreover have <fact2> by <method>
      {* more steps here *}
      moreover have <factn> by <method>
      ultimately have <conclusion> by <method>
  You can use the "print_facts" command to display the known facts. 
*)
lemma "l @ [] = l"
proof (induction l) print_cases
  case Nil thus ?case using append.simps(1) .
next
  case (Cons x l) print_facts thm append.simps(2)
    (* [of v1 v2 ... vn] substitutes terms v1 ... vn to the n first variables of a fact *)
    from append.simps(2)[of "x" "l" "[]"] have "(x # l) @ [] = x # (l @ [])" .
    also with Cons.IH have "... = (x # l)" by simp
    finally show ?case .
qed
 
(* Associativity of append *)
(* Here, we illustrate another style of proof, where proof methods
   are applied until all goals have been discharged.
   The proof is closed by the "done" keyword.
*)
lemma append_assoc: "(l1 @ l2) @ l3 = l1 @ (l2 @ l3)"
  apply (induction l1)
  (* The initial goal has been split into two goals: the base case and the inductive case *)
  apply simp  (* Here, simp gets rid of the base case *)
  apply simp  (* and the last goal is solved again by simp *)
done
 
(* This can be written is a more compact way. "simp+" means "apply simp as much as you can". *)
lemma "(l1 @ l2) @ l3 = l1 @ (l2 @ l3)"
by (induction l1, simp+)
 
(* Structured proof of the same lemma *)
lemma "(l1 @ l2) @ l3 = l1 @ (l2 @ l3)"
proof (induction l1) print_cases
  case Nil
    from append.simps(1) have "([] @ l2) = l2" .
    hence "([] @ l2) @ l3 = l2 @ l3" by simp
    (* [symmetric] applies symmetry to an equality *)
    also from append.simps(1)[symmetric] have "... = [] @ l2 @ l3" .
    finally show ?case .
next
  case (Cons x l) print_facts
    from append.simps(2) have "((x # l) @ l2) @ l3 = x # (l @ l2) @ l3" by simp
    also from Cons.IH have "... = x # l @ (l2 @ l3)" by simp
    finally show ?case by simp
qed
 
(* Lemma about reversing the concatenation of two lists *)
lemma rev_append: "rev (l1 @ l2) = (rev l2) @ (rev l1)"
  apply (induct l1)
  apply simp
  apply auto  (* Here, auto simplifies the goal but does not solve it. *)
  thm append_assoc  (* This theorem about the associativity of '@' will solve the goal. *)
  apply (rule append_assoc)
done
 
(* Compact form, where "auto simp add <rule>" means "apply auto,
   adding <rule> to the rules the simplifier can use.
*)
lemma "rev (l1 @ l2) = (rev l2) @ (rev l1)"
by (induction l1, auto simp add:append_assoc)
 
(* Detailed structured proof of the same lemma *)
lemma "rev (l1 @ l2) = (rev l2) @ (rev l1)"
proof (induction l1) print_cases
  case Nil
    from append.simps(1)[of l2] have "rev ([] @ l2) = rev l2" by simp
    also from append_nil[of "(rev l2)", symmetric] have "... = (rev l2) @ []" by simp
    also from rev.simps(1) have "... = (rev l2) @ (rev [])" by simp
    finally show ?case .
next
  case (Cons x l) print_facts
    from append.simps(2)[of x l l2] have "(x # l) @ l2 = x # (l @ l2)" .
    hence "rev ((x # l) @ l2) = rev (x # (l @ l2))" by simp
    also from rev.simps(2)[of x "l @ l2"] have "... = rev (l @ l2) @ x # []" .
    also from Cons.IH have "... = (rev l2 @ rev l) @ x # []" by simp
    also from append_assoc[of "rev l2" "rev l" "x # []"] have "... = rev l2 @ rev l @ x # []" .
    also from rev.simps(2)[of x "[]", symmetric] and rev.simps(1) have "... = rev l2 @ rev (x # l)" by simp
    finally show ?case .
qed
 
(*
  Prove that rev is the inverse of itself, using the previous lemmas
 
  Theorems and lemma are the same from the point of view of Isabelle.
  Lemmas are just theorems of less importance to us.
*)
theorem rev_rev: "rev (rev l) = l"
  apply (induct l)
  apply simp
  apply (auto simp add: append_assoc rev_append)
done
 
(* Structured proof of the same theorem *)
theorem "rev (rev l) = l"
proof (induction l) print_cases
  case Nil (* show ?case by simp *)
    from rev.simps(1) have "rev Nil = Nil" .
    hence "rev (rev Nil) = Nil" by simp
    thus ?case .
next
  case (Cons x l) print_facts
    have "rev (rev (x # l)) = rev ((rev l) @ (x # []))" by simp
    also have "... = rev (x # []) @ rev (rev l)" using rev_append .
    also from Cons.IH have "... = rev (x # []) @ l" using rev_rev by simp
    also have "... = (rev [] @ (x # [])) @ l" by simp
    also have "... = rev [] @ ((x # []) @ l)" using append_assoc by simp
    also have "... = [] @ (x # []) @ l" by simp
    also have "... = (x # []) @ l" by simp
    also have "... = x # ([] @ l)" by simp
    also have "... = x # l" by simp
    finally show ?case .
qed
 
(* Length of a list *)
fun len:: "'a list ⇒ nat"
where
  "len [] = 0"
| "len (x # l) = Suc (len l)"
 
(* Show that the length of the concatenation of two lists is the sum of their lengths *)
theorem append_len: "len (l1 @ l2) = (len l1) + (len l2)"
by (induction l1, simp+)
 
(* Structured proof, not very detailed *)
theorem "len (l1 @ l2) = (len l1) + (len l2)"
proof (induction l1) print_cases
  case Nil show ?case by simp
next
  case Cons thus ?case by simp
qed
 
(* The usual "map" operation, which applies a function to the elements of a list *)
fun map:: "('a ⇒ 'a) ⇒ 'a list ⇒ 'a list"
where
  "map f [] = []"
| "map f (x # l) = (f x) # (map f l)"
 
(* "abbreviation" defines a constant *)
abbreviation l4:: "int list"
where "l4 ≡ 1 # 2 # 3 # 4 # []"
 
(*
  Build the list of the squares of l4.
 
  λx. x*x is the function which takes an argument and returns its square.
*)
value "map (λx. x*x) l4"
 
(* Same thing with a function defined explicitly *)
definition square:: "int ⇒ int"
where "square n = n * n"
 
value "map square l4"
 
end
