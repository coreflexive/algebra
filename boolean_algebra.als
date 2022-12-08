open definitions

pred boolean_algebra(s: set univ, mt,jn: s->s->s, ng: s->s, z,u: s) {
  binop[s,mt]
  binop[s,jn]

  unop[s,ng]

  -- (13) identity laws
  right_identity[s, mt, u]
  right_identity[s, jn, z]

  -- (14) complement laws
  complementary[s,mt,ng,z]
  complementary[s,jn,ng,u]

  -- (18) commutative laws
  commutative[s,mt]
  commutative[s,jn]

  -- (20) distributive laws
  distl[s,mt,jn]
  distl[s,jn,mt]
}

pred complementary(s: set univ, f: s->s->s, g: s->s, y: s) {
  all x: s | f[x,g[x]] = y
}

pred demorgan_mt(s: set univ, mt,jn: s->s->s, ng: s->s) {
  all x,y: s | ng[mt[x,y]] = jn[ng[x],ng[y]]
}

pred demorgan_jn(s: set univ, mt,jn: s->s->s, ng: s->s) {
  all x,y: s | ng[jn[x,y]] = mt[ng[x],ng[y]]
}


