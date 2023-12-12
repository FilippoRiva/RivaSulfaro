sig Email {}
sig Username {}
sig Password {}

abstract sig User {
	username : disj one Username,
	email : disj one Email,
	password: one Password
}
sig Student extends User {
	//teams : set Team,
	//kts : set KataTournament
}
sig Team {
	players: disj some Student,
	//kb : one KataBattle,
	solution : disj one TeamKataSolution
}

sig Educator extends User {}
sig Organizer extends Educator{
	kbs : some KataBattle,
	//kts : some KataTournament
}
sig Owner extends Organizer {}

sig KataTournament {
	owner : one Owner,
	//organizers: some Organizer,
	//kbs : set KataBattle,
	students : set Student
}
sig KataBattle {
	kt : one KataTournament,
	teams : set Team,
	//organizer : one Organizer,
	code : disj one CodeKata
}
sig CodeKata {
	//kb : one KataBattle,
	//solutions : set TeamKataSolution
}
sig TeamKataSolution {
	//team : one Team,
	code : one CodeKata
}

pred show {
	#Team = 3
	#Student = 6
	#KataBattle = 2
}

run show for 10 
