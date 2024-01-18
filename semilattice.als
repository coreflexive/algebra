open operator_tax

pred semilattice(s: set univ, f: s->s->s) {
	semigroup[s,f]

	idempotent[s,f]
	commutative[s,f]
}
