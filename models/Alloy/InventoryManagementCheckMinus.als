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

pred shippingOrReceiving[its, its': Inventory, itemId: ItemId, quantity: Int] {
	plus[its.itemDB[itemId].count, quantity] < 0 implies {
		all itemId': ItemId | its'.itemDB[itemId'] = its.itemDB[itemId']
	}
	else {
		some it': Item | {
			no itemId2: ItemId | its.itemDB[itemId2] = it'
			its'.itemDB = its.itemDB ++ itemId -> it'
			it'.name = its.itemDB[itemId].name
			it'.count = plus[its.itemDB[itemId].count, quantity] 
		}
	}
}

pred execute[] {
    some disj its, its', its'', its''': Inventory, itemId: ItemId, n: Name | {
		init[its]
		itemRegistration[its, its', itemId, 100, n]
		shippingOrReceiving[its', its'', itemId, -50]
		shippingOrReceiving[its'', its''', itemId, -75]
	}
}

run execute for 2 but 4 Inventory, 8 Int
