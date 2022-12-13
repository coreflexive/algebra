open operator_tax

pred boolean_algebra(s: set univ, mt,jn: s->s->s, ng: s->s, z,u: s) {
  binop[s,mt]
  binop[s,jn]
  unop[s,ng]

  -- (11)
  ng[z] = u
  ng[u] = z

  -- (12)
  right_zero[s,mt,z]
  right_zero[s,jn,u]

  -- (13)
  right_identity[s, mt, u]
  right_identity[s, jn, z]

  -- (14)
  complementary[s,mt,ng,z]
  complementary[s,jn,ng,u]

  -- (15)
  involution[s,ng]

  -- (16)
  idempotent[s,mt]
  idempotent[s,jn]

  -- (17)
  demorgan[s,mt,jn,ng]
  demorgan[s,jn,mt,ng]

  -- (18)
  commutative[s,mt]
  commutative[s,jn]

  -- (19)
  associative[s,mt]
  associative[s,jn]

  -- (20)
  distl[s,mt,jn]
  distl[s,jn,mt]
}

pred boolean_algebra_alt(s: set univ, mt,jn: s->s->s, ng: s->s, z,u: s) {
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

pred demorgan(s: set univ, f,g: s->s->s, ng: s->s) {
  all x,y: s | ng[f[x,y]] = g[ng[x],ng[y]]
}

