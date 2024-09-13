sig ItemId, Name{}
sig Inventory {
	itemDB: ItemId lone -> lone Item
}
sig Item {
	name : Name,
	count: Int
}

pred init[its: Inventory] {
	no its.itemDB
}

pred itemRegistration[its, its': Inventory, itemId: ItemId, quantity: Int, n: Name] {
	some it: Item |	{
		no itemId2: ItemId | its.itemDB[itemId2] = it
		its'.itemDB = its.itemDB + itemId -> it
		it.name = n
		it.count = quantity
	}
}

pred shipping[its, its': Inventory, itemId: ItemId, quantity: Int] {
	some it': Item | {
		no itemId2: ItemId | its.itemDB[itemId2] = it'
		its'.itemDB = its.itemDB ++ itemId -> it'
		it'.name = its.itemDB[itemId].name
		it'.count = minus[its.itemDB[itemId].count, quantity] 
	}
}

pred receiving[its, its': Inventory, itemId: ItemId, quantity: Int] {
	some it': Item | {
		no itemId2: ItemId | its.itemDB[itemId2] = it'
		its'.itemDB = its.itemDB ++ itemId -> it'
		it'.name = its.itemDB[itemId].name
		it'.count = plus[its.itemDB[itemId].count, quantity] 
	}
}

pred execute[] {
	some disj its, its', its'', its''': Inventory, itemId: ItemId, n: Name | {
		init[its]
		itemRegistration[its, its', itemId, 100, n]
		shipping[its', its'', itemId, 50]
		receiving[its'', its''', itemId, 25]
	}
}

run execute for 2 but 4 Inventory, 3 Item, 8 Int
