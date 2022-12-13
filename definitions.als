pred binop(s: univ, f: s->s->s) {
  f in (s->s) -> one s
}

pred unop(s: set univ, f: s->s) {
  f in s -> one s
}



pred associative(s: univ, f: s->s->s) {
  all a,b,c: s {
    f[f[a,b],c] = f[a,f[b,c]]
  }
}

pred commutative(s: univ, f: s->s->s) {
  all a,b: s {
    f[a,b] = f[b,a]
  }
}

pred idempotent(s: univ, f: s->s->s) {
  all a: s {
    f[a,a] = a
  }
}

pred left_zero(s: univ, f: s->s->s, z: s) {
  all p: s | f[z,p] = z
}

pred right_zero(s: univ, f: s->s->s, z: s) {
  all p: s | f[p,z] = z
}

pred zero(s: univ, f: s->s->s, z: s) {
  left_zero[s,f,z]
  right_zero[s,f,z]
}

pred left_identity(s: set univ, f: s->s->s, l: s) {
  all a: s {
    f[l,a] = a
  }
}

pred right_identity(s: set univ, f: s->s->s, r: s) {
  all a: s {
    f[a,r] = a
  }
}

pred identity(s: set univ, f: s->s->s, e: s) {
  left_identity[s,f,e]
  right_identity[s,f,e]
}

pred left_inverse(s: set univ, f: s->s->s, e,l,a: s) {
  identity[s,f,e]
  f[l,a] = e
}

pred right_inverse(s: set univ, f: s->s->s, e,r,a: s) {
  identity[s,f,e]
  f[a,r] = e
}

pred inverse(s: set univ, f: s->s->s, e,b,a: s) {
  identity[s,f,e]
  left_inverse[s,f,e,b,a]
  right_inverse[s,f,e,b,a]
}

pred self_inverse(s: set univ, f: s->s->s, e: s) {
  all p: s | f[p,p] = e
}

pred complementary(s: set univ, f: s->s->s, g: s->s, y: s) {
  all x: s | f[x,g[x]] = y
}

pred distl(s: set univ, f,g: s->s->s) {
  all a,b,c: s {
    f[a,g[b,c]] = g[f[a,b],f[a,c]]
  }
}

pred distr(s: set univ, f,g: s->s->s) {
  all a,b,c: s {
    f[g[b,c],a] = g[f[b,a],f[c,a]]
  }
}

pred involution(s: set univ, f: s->s) {
  all x: s | f[f[x]] = x
}
