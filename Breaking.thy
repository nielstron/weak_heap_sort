theory Breaking
imports"HOL-Library.Tree"   "HOL-Library.Pattern_Aliases"
begin
context includes pattern_aliases
begin

type_synonym 'a weird_tree = "'a \<times> (bool\<times>'a) tree"

fun weird_comb:: "'a::linorder weird_tree \<Rightarrow> 'a::linorder weird_tree" where
"weird_comb (a, Leaf) = (a, Leaf)" |
"weird_comb (ai, \<langle>lj, (ij, aj), rj\<rangle>) = (
  if ai \<le> aj then (ai, \<langle>lj, (ij,aj), rj\<rangle>) else (aj, \<langle>lj, (\<not>ij,ai), rj\<rangle>)
)"

fun not_so_weird_siwn::"'a::linorder weird_tree \<Rightarrow> 'a::linorder weird_tree" where
 "not_so_weird_siwn (a, Leaf) = (a, Leaf)" |
 "not_so_weird_siwn (a, \<langle>l, x, r\<rangle>) = (case x of (False, _) \<Rightarrow>
    (case not_so_weird_siwn (a, l) of (a', l') \<Rightarrow>  weird_comb (a', \<langle>l', x, r\<rangle>))
| (True, _) \<Rightarrow>
    (case not_so_weird_siwn (a, l) of (a',l') \<Rightarrow> (a', \<langle>l, x, l'\<rangle>))
)"

fun weird_siwn::"'a::linorder weird_tree \<Rightarrow> 'a::linorder weird_tree" where
 "weird_siwn (a, Leaf) = (a, Leaf)" |
 "weird_siwn (a, \<langle>l, x, r\<rangle>) = (case x of (False, _) \<Rightarrow>
    (let (a', l') = weird_siwn (a, l) in  weird_comb (a', \<langle>l', x, r\<rangle>))
| (True, _) \<Rightarrow>
    (let (a', l') =  weird_siwn (a, l) in weird_comb (a', \<langle>l', x, r\<rangle>))
)"
end
end