open definitions

pred magma(s: univ, f: s->s->s) {
  f in s->s->s
}

pred semigroup(s: univ, f: s->s->s) {
  binop[s,f]
  associative[s,f]
}

pred monoid(s: univ, f: s->s->s, e: s) {
  semigroup[s,f]
  identity[s,f,e]
}

pred group(s: univ, f: s->s->s, e: s) {
  monoid[s,f,e]
  all x: s | some y: s | inverse[s,f,e,y,x]
}
