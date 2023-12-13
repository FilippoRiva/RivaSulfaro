sig Email {}{
	one this.~email
}
sig Username {}{
	one this.~username
}
//sig Password {}

abstract sig User {
	username : disj one Username,
	email : disj one Email,
	//password: one Password
}
sig Student extends User {
	//teams : set Team,
	//kts : set KataTournament
}{
	one this.~students
}

sig Team {
	players : some Student,
	kb : one KataBattle,
	solution : disj one TeamKataSolution
}

sig Educator extends User {}

sig KataTournament {
	owner : one Educator,
	organizers: some Educator,
	//kbs : disj set KataBattle,
	students : set Student
}{
	owner in organizers
}


sig KataBattle {
	kt : one KataTournament,
	//teams : set Team,
	organizer : one Educator,
	code : disj one CodeKata
}
sig CodeKata {
	//kb : one KataBattle,
	solutions : disj set TeamKataSolution
}{
	one this.~code
}
sig TeamKataSolution {
	//team : one Team,
	//code : one CodeKata
}{
	one this.~solution
	one this.~solutions
}

fact KataSolutionForSpecificKB {
	all t : Team | t.solution in t.kb.code.solutions
}

fact DistinctStudentInSameKB {
	all t1:Team, t2: Team, s: Student |
      (t1 != t2 and s in t1.players and s in t2.players) implies
      t1.kb != t2.kb
}

pred show2 {
	#TeamKataSolution = 4
	#CodeKata = 3
}

run show2 for 8
