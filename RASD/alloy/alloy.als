abstract sig Boolean {}
lone sig True extends Boolean {}
lone sig False extends Boolean {}
sig DateTime {
    time: one Int
}{
    time >= 0
}

sig Email {}{
    one this.~email
}
sig Username {}{
	one this.~username
}
sig Password {}{
    some this.~password
}
sig Description {}{
//  one this.~descriptionKT
//  one this.~descriptionCode
}
sig GitHubRepo {}{
}
//project, testCases, scripts
sig Code {}{
	one this.~code
}

abstract sig User {
    username : disj one Username,
    email : disj one Email,
    password: one Password
}
sig Student extends User {
//  ktrs : set KTRank
}
sig Educator extends User {}

sig KataTournament {
    owner : one Educator,
    organizers: some Educator,
    descriptionKT : one Description,
    students : set Student
}{
    owner in organizers
}

sig TeamKataSolution {
    code : disj one Code,
    score : one Int
}{
    one this.~solution
    one this.~solutions
    score >= 0 //and score <= 100
    //int cannot be that big
}
sig CodeKata {
    solutions : disj set TeamKataSolution,
    descriptionCode : one Description,
    gitHubRepoKata : disj one GitHubRepo
}{
    one this.~code
}

sig Team {
    players : some Student,
    kb : one KataBattle,
    solution : disj one TeamKataSolution,
    battleRank : one Int,
    gitHubRepoTeam : disj one GitHubRepo
}{
    battleRank >= 1 and battleRank <= #(kb.teams)
}
sig KataBattle {
    kt : one KataTournament,
 	organizer : one Educator,
 	code : disj one CodeKata,
 	minTeamSize : one Int,
 	maxTeamSize : one Int,
 	registrationDeadline : one DateTime,
 	submissionDeadline : one DateTime,
 	isManualEvaluationNeeded : one Boolean,
 	teams : set Team
}{
    minTeamSize > 0
    maxTeamSize >= minTeamSize
    submissionDeadline.time > registrationDeadline.time
    teams = {t : Team | t.kb = this}
}

fact gitHubRepoAreAllDifferent{
    all t : Team, ck : CodeKata |
    ck.gitHubRepoKata != t.gitHubRepoTeam
}

fact RankProperlyBasedOnScore{
	all t1, t2 : Team | t1 != t2 and t1.kb = t2.kb implies (t1.battleRank != t2.battleRank and
	(t1.solution.score < t2.solution.score implies t1.battleRank > t2.battleRank))
}

fact ProperTeamSize{
	all kb : KataBattle | all t : kb.teams |
	#t.players >= kb.minTeamSize and #t.players <= kb.minTeamSize
}

fact KataSolutionForSpecificKB {
	all t : Team | t.solution in t.kb.code.solutions
}

fact DistinctStudentInSameKB {
	all t1:Team, t2: Team, s: Student |
      (t1 != t2 and s in t1.players and s in t2.players) implies
      t1.kb != t2.kb
}

fact OrganizersOfKBAreAlsoOfKT {
	all kb : KataBattle | kb.organizer in kb.kt.organizers
}

fact StudentInTeamAreSubscribedToKT {
	all t : Team |
	t.players in t.kb.kt.students
}



//fact OneKTRForKT {
//	all ktr1, ktr2 : KTRank |
//	(ktr1 != ktr2 and ktr1.tournament = ktr2.tournament) implies ktr1.student != ktr2.student
//}
//sig KTRank {
//	ktRank : one Int,
//	tournament : one KataTournament
//}{
//	ktRank >= 1
//	one this.~ktrs
	//and ktRank <= #(ktt.ktRanks)
//}

//fact StudentsInKTHaveRanks {
//	all kb2 : KataBattle, ktr : KTRank |
//		all t : kb2.teams |
//				ktr.student in t.players implies (ktr in kb2.kt.ktRanks)
//}

//fact ReverseS
//fact EachStudentInTeamHasKTRank {
//    all t : Team, s : Student |
//        s in t.players implies #(s.ktrs) = //
// implies one ktr : KTRank | ktr.student = s and ktr.tournament = t.kb.kt
//}


pred show2 {
	#Team = 2
	#KataBattle = 1
	#KataTournament = 2
}

run show2 for 8
