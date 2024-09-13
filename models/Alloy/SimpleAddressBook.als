sig Name, Addr {}
sig Book {
	owner: Name,
	addr: Name -> lone Addr
}

pred init[b: Book, n: Name] {
	b.owner = n
	no b.addr
}

pred add[b, b': Book, n: Name, a: Addr] {
	b'.owner = b.owner
	b'.addr = b.addr + n -> a
}

pred del[b, b': Book, n: Name] {
	b'.owner = b.owner
	b'.addr = b.addr - n -> b.addr[n]
}

pred execute[] {
	some disj b0, b1, b2, b3: Book, disj n0, n1, n2: Name, a0, a1: Addr | {
		init[b0, n0]
		add[b0, b1, n1, a0]
		add[b1, b2, n2, a1]
		del[b2, b3, n1
	}
}

run execute for 2 but 4 Book, 3 Name
