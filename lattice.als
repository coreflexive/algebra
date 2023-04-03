open semilattice

pred lattice(s: set univ, mt,jn: s->s->s){
  semilattice[s,mt]
  semilattice[s,jn]

	absorption[s,mt,jn]
	absorption[s,jn,mt]
}
