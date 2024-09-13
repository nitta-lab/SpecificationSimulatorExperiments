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

pred receivingOrShipping[its, its': Inventory, itemId: ItemId, quantity: Int] {
	some it': Item | {
		no itemId2: ItemId | its.itemDB[itemId2] = it'
		its'.itemDB = its.itemDB ++ itemId -> it'
		it'.name = its.itemDB[itemId].name
		it'.count = plus[its.itemDB[itemId].count, quantity]
	}
}

pred execute[] {
	some disj its, its', its'': Inventory, itemId: ItemId, n: Name | {
		init[its]
		itemRegistration[its, its', itemId, 100, n]
		receivingOrShipping[its', its'', itemId, -50]
	}
}

run execute for 2 but 3 Inventory, 8 Int
