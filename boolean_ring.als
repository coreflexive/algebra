open ringoid_tax

pred boolean_ring(s: set univ, tms,pls: s->s->s, e,u: s){
  unit_ring[s,tms,pls,e,u]

  idempotent[s,tms]
}
