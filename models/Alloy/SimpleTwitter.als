sig AccountId, Name, Tweet { }
sig Accounts {
	accountDB: AccountId lone -> lone Account
}
sig Account {
	name: Name,
	tweets: List
}

sig List {
	size: Int,
	element: Int -> lone Tweet
}

pred init[acs: Accounts] {
	no acs.accountDB
}

pred signUp[acs, acs': Accounts, id: AccountId, n: Name] {
	some ac: Account | {
		no id2: AccountId | acs.accountDB[id2] = ac
		acs'.accountDB = acs.accountDB + id -> ac
		ac.name = n
		ac.tweets.size = 0
		no ac.tweets.element
	}
}

pred tweet[acs, acs': Accounts, id: AccountId, contents: Tweet] {
	some ac': Account | {
		no id2: AccountId | acs.accountDB[id2] = ac'
		acs'.accountDB = acs.accountDB ++ id -> ac'
		ac'.name = acs.accountDB[id].name
		ac'.tweets != acs.accountDB[id].tweets
		ac'.tweets.size = plus[acs.accountDB[id].tweets.size, 1]
		ac'.tweets.element[minus[ac'.tweets.size, 1]] = contents
		all n: Int | n != minus[ac'.tweets.size, 1] implies ac'.tweets.element[n] = acs.accountDB[id].tweets.element[n]
	}
}

pred execute[] {
	some disj acs, acs', acs'': Accounts, id: AccountId, n: Name, contents: Tweet | {
		init[acs]
		signUp[acs, acs', id, n]
		tweet[acs', acs'', id, contents]
	}
}

run execute for 2 but 3 Accounts
