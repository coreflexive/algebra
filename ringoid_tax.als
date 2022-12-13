open operator_tax

pred ringoid(s: set univ, tms,pls: s->s->s){
  distl[s,tms,pls]
  distr[s,tms,pls]
}

pred semiring(s: set univ, tms,pls: s->s->s){
  ringoid[s,tms,pls]
  
  semigroup[s,pls]
  commutative[s,pls]

  semigroup[s,tms]
}

pred ring(s: set univ, tms,pls: s->s->s, e: s){
  ringoid[s,tms,pls]

  group[s,pls,e]
  commutative[s,pls]

  semigroup[s,tms]
}

pred unit_ring(s: set univ, tms,pls: s->s->s, e,u: s){
  ring[s,tms,pls,e]

  right_identity[s,tms,u]
}
