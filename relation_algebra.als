open boolean_algebra

pred relation_algebra(a: set univ, pls,mul: a->a->a, cmp,cnv: a->a, id: a) {
  binop[a,pls]
  binop[a,mul]
  unop[a,cmp]
  unop[a,cnv]

  commutative[a,pls] -- (R1)

  associative[a,pls] -- (R2)

  huntington[a,pls,cmp] -- (R3)

  associative[a,mul] -- (R4)

  right_identity[a,mul,id] -- (R5)

  involution[a,cnv] -- (R6)

  contravariant[a,mul,cnv] -- (R7)

  distr[a,mul,pls] -- (R8)

  bilinear[a,pls,cnv] -- (R9)

  tarski[a,pls,mul,cmp,cnv] -- (R10)
}

pred huntington(a: set univ, pls: a->a->a, cmp: a->a) {
  all r,s: a | pls[cmp[pls[cmp[r],s]],cmp[pls[cmp[r],cmp[s]]]] = r
}

pred tarski(a: set univ, pls,mul: a->a->a, cmp,cnv: a->a) {
  all r,s: a | pls[mul[cnv[r],cmp[mul[r,s]]],cmp[s]] = cmp[s]
}

pred bilinear(a: set univ, pls: a->a->a, cnv: a->a) {
  all r,s: a | cnv[pls[r,s]] = pls[cnv[r],cnv[s]]
}

pred contravariant(a: set univ, mul: a->a->a, cnv: a->a) {
  all r,s: a | cnv[mul[r,s]] = mul[cnv[s],cnv[r]]
}
