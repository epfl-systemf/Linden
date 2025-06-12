# Quantifier rewrites from regexp-tree
FROM: https://github.com/DmitrySoshnikov/regexp-tree/tree/master/src/optimizer

## r{m}r{n} ~ r{m+n}
## r{m}r{0,n} ~ r{m,m+n}
## r{m}r{0,n}? ~ r{m,m+n}?
## r{0,m}r{n} ~ r{n,m+n}
FALSE, reported to regexp-tree
## r{0,m}r{0,n} ~ r{0,m+n}
## r{0,m}?r{0,n}? ~ r{0,m+n}?
FALSE, reported to regexp-tree

All of the r{0,n} stuff can be extended to stars with the same results.

# Other rewrites from regexp-tree
FROM: https://github.com/DmitrySoshnikov/regexp-tree/tree/master/src/optimizer

## (?:) ~ epsilon
## unicode pairs
## simpler char codes
## lower case when using flag i
## remove duplicates in char classes
## merge adjacent ranges
## use character class escapes
## from char class to single char
## remove unnecessary escapes
## dijsunction to char classes a|b ~ [ab]


# Anchors/lookaround rewrites

## ^ ~ (?<!True)
FROM: https://www.microsoft.com/en-us/research/wp-content/uploads/2025/01/cpp24-final.pdf (Section 6.2)
PROVED

## $ ~ (?!True)
FROM: https://www.microsoft.com/en-us/research/wp-content/uploads/2025/01/cpp24-final.pdf (Section 6.2)
PROVED

## \b ~ (?<!\w)(?=\w)|(?<=\w)(?!=\w)
FROM: https://www.microsoft.com/en-us/research/wp-content/uploads/2025/01/popl25-p2-final.pdf
"a unique zero-cost implementation of the word boundary \b – represented via negative lookarounds"
PROVED

## \B ~ ((?<=\w)|(?!=\w))((?<!\w)|(?=\w))
PROVED

# Strictly nullable optimization
## r* ~ epsilon
FROM: https://dl.acm.org/doi/10.1145/3674666 (Section 5)
TODO

# Traditional rewrites
FROM: https://dl.acm.org/doi/10.1017/s0956796808007090

## r|r ~ r
FALSE https://dl.acm.org/doi/10.1145/3674666 (Fig 21)
Could be fixed if r has no group
Seems to be used in regexp-tree as well. TODO: check what they do with groups
## r|s ~ s|r
FALSE with r=a, s=ab, string="ab"
## (r|s)|t ~ r|(s|t)
## False|r ~ r
## True|r ~ True
FALSE if True = Epsilon
## (r.s).t ~ s.(s.t)
## True.r ~ r
## r.True ~ r
## False.r ~ False
## r.False ~ False
## (r*)* ~ r*
## epsilon* ~ epsilon
Consequence of strictly nullable
## False* ~ epsilon
Consequence of strictly nullable

# Question mark rewrites
FROM https://dl.acm.org/doi/10.1145/3674666 (Fig 21)

## r? ~ r|epsilon
FALSE
## r?? ~ epsilon|r
FALSE
Could be true without backreferences

# Distributivity rewrites
FROM https://dl.acm.org/doi/10.1145/3632934 (Lemma 10)

## r1.(r2|r3) ~ r1.r2 | r1.r3
## (r1|r2).r3 ~ r1.r3 | r2.r3
FALSE

# Lookaround rewrites
FROM https://dl.acm.org/doi/10.1145/3632934 (Lemma 11)

## (?=r1)(?=r2) ~ (?=r2)(?=r1)
FALSE if a backref in r2 refers to a group in r1
## (?=r1)(?=r1) ~ (?=r1)
FALSE (I think) with a backref, or if it duplicates a group. Same as r|r ~ r.
## (?=r)* ~ epsilon
Consequence of strictly nullable
## (?=r1|r2) ~ (?=r1)|(?=r2)
## (?=(?=r)s) ~ (?=r)(?=s)
## (?=r(?=s).*) ~ (?=rs)
## (?=r)|(?!=r) ~ epsilon
## (?=r)(?!=r) ~ False
MAYBE FALSE with a backref. The first lookahead defines a group which prevents the second from matching

