sig Email {}
sig Username {}
sig Password {}
sig Description {}

sig Student {
	username : one Username,
	email : one Email,
	password: one Password
}
sig Team {
	player: disj some Student
	//kb?
}

sig Educator {
	username : one Username,
	email : one Email,
	password: one Password
}
sig Organizer extends Educator{}
sig Owner extends Organizer {}

sig KataTournament {
	owner : one Owner,
	organizer: set Organizer,
	description : one Description
}
sig KataBattle {
	kt : one KataTournament,
	teams : set Team
}
