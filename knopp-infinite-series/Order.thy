theory Order
  imports Main Natural
begin

-- "An ordering based on <, = and > having the laws defined in chapter 1"

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

class order =
  fixes lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "<" 50)
  assumes exclusive:
    "(a < b) = (\<not> a = b \<and> \<not> (b < a))"
    "(a = b) = ((\<not> (a < b)) \<and> (\<not> (b < a)))"
    "(b < a) = ((\<not> (a < b)) \<and> (\<not> (a = b)))"
  assumes trans:
    "\<not> (b < a) \<Longrightarrow> (b < c) \<Longrightarrow> (a < c)"
    "(a < b) \<Longrightarrow> \<not> (c < b) \<Longrightarrow> (a < c)"

definition (in order) gt (infix ">" 50) where
  "a > b = (b < a)"
declare order.gt_def [simp]

definition le (infix "\<le>" 50) where
  "a \<le> b = (\<not> b < a)"
declare le_def [simp]

definition ge (infix "\<ge>" 50) where
  "a \<ge> b = (\<not> a < b)"

declare ge_def [simp]

instantiation natural :: order
begin

fun lt_natural where
  "lt_natural one (succ _) = True" |
  "lt_natural (succ a) (succ b) = lt_natural a b" |
  "lt_natural _ _ = False"

instance proof
  fix a b c :: natural
  show "(a < b) = (a \<noteq> b \<and> \<not> b < a)"
       "(a = b) = (\<not> a < b \<and> \<not> b < a)"
       "(b < a) = (\<not> a < b \<and> a \<noteq> b)"
    using lt_natural.elims(3)
    by (induction a b rule: lt_natural.induct; auto+)+
  show "\<not> b < a \<Longrightarrow> b < c \<Longrightarrow> a < c"
       "a < b \<Longrightarrow> \<not> c < b \<Longrightarrow> a < c"
    by (induction a c arbitrary: b rule: lt_natural.induct; auto;
        metis natural.distinct(1) natural.inject lt_natural.elims(2) lt_natural.elims(3))+
qed

end

end