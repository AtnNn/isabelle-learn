theory RealNumbersAndSequences
  imports Main
begin

chapter "I. Principles of the theory of real numbers"
  
section "1. The system of rational numbers and its gaps"

no_notation Orderings.less (infix "<" 50)
no_notation Orderings.greater (infix ">" 50)
no_notation Orderings.less  ("(_/ < _)"  [51, 51] 50)
no_notation less_eq  ("op <=")
no_notation less_eq  ("(_/ \<le> _)" [51, 51] 50)
no_notation greater_eq  (infix "\<ge>" 50)

no_notation plus (infixl "+" 65)
no_notation minus (infixl "-" 65)
no_notation uminus ("- _" [81] 80)
no_notation times (infixl "*" 70)
no_notation inverse_divide (infixl "'/" 70)

datatype natural = one | succ natural
  
(* declare [[show_types]] *)

class order =
  fixes lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "<" 50)
  fixes gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix ">" 50)
  assumes exclusive:
    "(a < b) = (\<not> a = b \<and> \<not> (a > b))"
    "(a = b) = ((\<not> (a < b)) \<and> (\<not> (a > b)))"
    "(a > b) = ((\<not> (a < b)) \<and> (\<not> (a = b)))"
  assumes trans:
    "\<not> (a > b) \<Longrightarrow> (b < c) \<Longrightarrow> (a < c)"
    "(a < b) \<Longrightarrow> \<not> (b > c) \<Longrightarrow> (a < c)"
    
definition le (infix "\<le>" 50) where
  "a \<le> b = (\<not> a > b)"
declare le_def[simp]

definition ge (infix "\<ge>" 50) where
  "a \<ge> b = (\<not> a < b)"
declare ge_def[simp]

instantiation natural :: order
begin

fun lt_natural where
  "one < succ _ = True" |
  "succ a < succ b = lt a b" |
  "lt_natural _ _ = False"

definition gt_natural :: "natural \<Rightarrow> natural \<Rightarrow> bool" where
  "gt_natural a b = (b < a)"
declare gt_natural_def[simp]

instance proof
  fix a b c :: natural
  show "(a < b) = (a \<noteq> b \<and> \<not> a > b)"
       "(a = b) = (\<not> a < b \<and> \<not> a > b)"
       "(a > b) = (\<not> a < b \<and> a \<noteq> b)"
    using lt_natural.elims(3) by (induction a b rule: lt_natural.induct, auto)+
  show "\<not> a > b \<Longrightarrow> b < c \<Longrightarrow> a < c"
       "a < b \<Longrightarrow> \<not> b > c \<Longrightarrow> a < c"
    by (induction a c arbitrary: b rule: lt_natural.induct; auto;
        metis natural.distinct(1) natural.inject lt_natural.elims(2) lt_natural.elims(3))+
qed

end

fun add_nat where
  "add_nat one n = succ n" |
  "add_nat (succ n) m = succ (add_nat n m)"

fun mul_nat where
  "mul_nat one n = n" |
  "mul_nat (succ n) m = add_nat m (mul_nat n m)"

fun succ_abs_diff_nat where
  "succ_abs_diff_nat one one = one" |
  "succ_abs_diff_nat one (succ b) = succ b" |
  "succ_abs_diff_nat (succ a) one = succ a" |
  "succ_abs_diff_nat (succ a) (succ b) = succ_abs_diff_nat a b"

lemma add_nat_commutative: "add_nat a b = add_nat b a"
proof (induction a b rule: add_nat.induct)
  fix n
  show "add_nat one n = add_nat n one"
  proof (simp, induction n one rule: add_nat.induct)
    show "succ one = add_nat one one" by simp
    fix n
    assume "succ n = add_nat n one"
    then have "succ (succ n) = succ (add_nat n one)" by simp
    then show "succ (succ n) = add_nat (succ n) one" try
      by (simp add: \<open>succ (succ n) = succ (add_nat n one)\<close>)
  qed
next
  fix n m
  assume IH: "add_nat n m = add_nat m n"
  have "succ (add_nat m n) = add_nat m (succ n)"
    by (induction m n rule: add_nat.induct, auto)
  then show "add_nat (succ n) m = add_nat m (succ n)" using IH by simp
qed
  
lemma "succ_abs_diff_nat a b = c \<Longrightarrow> add_nat c a = succ b \<or> add_nat c b = succ a"
  apply (induction a b rule: succ_abs_diff_nat.induct)
  apply (auto simp add: add_nat_commutative)
  done

fun gcd_nat where
  "gcd_nat a b = (
    case succ_abs_diff_nat a b of
      one \<rightarrow> a
    | succ c \<rightarrow> gcd_nat b c)"

typedecl rational

axiomatization zero_rational :: rational
  and quotient :: "bool \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> rational"
  where quotient_neq_zero: "zero_rational \<noteq> quotient s a b"
    and quotient_eq: "s = t \<Longrightarrow> mul_nat a d = mul_nat b c \<Longrightarrow>
                      quotient s a b = quotient t c d"

-- "Fundamental Laws of Order"
 
theorem 1:
  "a = a"
  "a = b \<Longrightarrow> b = a"
  "a = b \<Longrightarrow> b = c \<Longrightarrow> a = c"
  "(a \<le> b \<and> b < c) \<or> (a < b \<and> b \<le> c) \<Longrightarrow> a < c"
  using order_class.trans by (auto, fastforce+)

class number = order +
  fixes add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
  fixes sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-" 65)
  fixes mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
  fixes div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "'/" 70)
  fixes zero :: "'a"
  assumes addition:
    "\<exists> c. a + b = c"
    "a = a' \<Longrightarrow> b = b' \<Longrightarrow> a + b = a' + b'"
    "a + b = b + a"
    "(a + b) + c = a + (b + c)"
    "a < b \<Longrightarrow> a + c < b + c"
  assumes subtraction:
    "\<exists> c. a + c = b"
    "a + c = b \<Longrightarrow> b - a = c"
  assumes multiplication:
    "\<exists> c. a * b = c"
    "a = a' \<Longrightarrow> b = b' \<Longrightarrow> a * b = a' * b'"
    "a * b = b * a"
    "(a * b) * c = a * (b * c)"
    "a < b \<Longrightarrow> c > zero \<Longrightarrow> a * c < b * c"
  assumes division:
    "a \<noteq> zero \<Longrightarrow> \<exists> c. a * c = b"
    "a \<noteq> zero \<Longrightarrow> a * c = b \<Longrightarrow> b / a = c"

instantiation rational :: order
begin

definition lt_rational :: "rational \<Rightarrow> rational \<Rightarrow> bool" where
  "lt_rational a b = "