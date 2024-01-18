open common

pred binop(s: set univ, f: s->s->s) {
  f in (s->s) -> one s
}

pred unop(s: set univ, f: s->s) {
  f in s -> one s
}

pred semigroup(s: set univ, f: s->s->s) {
  binop[s,f]
  associative[s,f]
}

pred monoid(s: set univ, f: s->s->s, e: s) {
  semigroup[s,f]
  identity[s,f,e]
}

pred group(s: set univ, f: s->s->s, e: s) {
  monoid[s,f,e]
  all x: s | some y: s | inverse[s,f,e,y,x]
}
