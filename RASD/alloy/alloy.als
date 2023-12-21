// SIGNATURES ----------------------------------------------------------------------------------------------------------

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

sig Description {}

sig GitHubRepo {}

//project, testCases, scripts
sig Code {}{
	one this.~code
}

abstract sig User {
	username : disj one Username,
	email : disj one Email,
	password: one Password
}

sig Educator extends User {}

sig Student extends User {}

sig KTRank {
	ktRank : one Int,
	tournament : one KataTournament,
	student : one Student
}{
	ktRank >= 1 and ktRank <= #(getKTRanks[tournament])
}

sig KataTournament {
	owner : one Educator,
	organizers: some Educator,
	descriptionKT : one Description
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
    battleRank >= 1 and battleRank <= #(getTeams[kb])
}

sig KataBattle {
	kt : one KataTournament,
	organizer : one Educator,
	code : disj one CodeKata,
	minTeamSize : one Int,
	maxTeamSize : one Int,
	registrationDeadline : one DateTime,
	submissionDeadline : one DateTime,
	isManualEvaluationNeeded : one Boolean
}{
	minTeamSize > 0
	maxTeamSize >= minTeamSize
	submissionDeadline.time > registrationDeadline.time
}

// PREDICATES ----------------------------------------------------------------------------------------------------------

//return true is the Student s is subscribed to the KataTournament kt2
pred isSubscribed [s : Student, kt2 : KataTournament] {
	some t : getTeams[s] | t.kb.kt = kt2
}



// FUNCTIONS ----------------------------------------------------------------------------------------------------------

//return all the solutions of a Student s in the KataTournament kt2
fun getSolutions [s : Student, kt2 : KataTournament] : TeamKataSolution {
	{ts: TeamKataSolution |some t : getTeams[s] | t.kb.kt = kt2 implies ts = t.solution}
}

//return the total score of a Student s in the KataTournament kt
fun studentScore [s : Student, kt : KataTournament] : Int {
	sum solution : getSolutions[s, kt]  | solution.score
}

//Reverse associations' functions-------------------------------------------

//return the teams of a Student s
fun getKTRanks [t : KataTournament] : KTRank {
	{ktr : KTRank | ktr.tournament = t}
}

//return the ktRanks of a Student s
fun getKTRanks [s : Student] : KTRank {
	{ktr : KTRank | ktr.student = s}
}

//return the teams of a Student s
fun getTeams [s : Student] : Team {
	{team : Team | s in team.players}
}

//return the teams of a Student s
fun getTeams [battle : KataBattle] : Team {
	{team : Team | team.kb = battle}
}

// FACTS ----------------------------------------------------------------------------------------------------------

//Every codeKata and every team must have different gitHub repository
fact gitHubRepoAreAllDifferent{
	all t : Team, ck : CodeKata |
	    ck.gitHubRepoKata != t.gitHubRepoTeam
}

//The battle rank for every team depends on the score of the team
fact RankProperlyBasedOnScore{
	all t1, t2 : Team | t1 != t2 and
	    t1.kb = t2.kb implies
	        (t1.battleRank != t2.battleRank and
	            (t1.solution.score < t2.solution.score implies
	                t1.battleRank > t2.battleRank))
}

//Every team has a number of student that respect the minimum and maximum imposed by the educator
fact ProperTeamSize{
	all kb : KataBattle | all t : getTeams[kb] |
	    #t.players >= kb.minTeamSize and #t.players <= kb.minTeamSize
}

//A solution of a team is also a solution for the problem of that KB
fact KataSolutionForSpecificKB {
	all t : Team | t.solution in t.kb.code.solutions
}

//A student can join only one team in a specific KB
fact DistinctStudentInSameKB {
	all t1:Team, t2: Team, s: Student |
        (t1 != t2 and s in t1.players and s in t2.players) implies
            t1.kb != t2.kb
}

//The educator that organize a KB organize also the KT
fact OrganizersOfKBAreAlsoOfKT {
	all kb : KataBattle | kb.organizer in kb.kt.organizers
}

//Each student that participate in a KB has a KTRank
fact EachStudentInTeamHasKTRank {
	all t : Team, s : Student |
		s in t.players implies
		    one ktr : KTRank | ktr.student = s and ktr.tournament = t.kb.kt
}

//The KTRank is only one per KT
fact UniqueKTRInSameKT {
	all ktr1, ktr2 : KTRank | 
		(ktr1.student = ktr2.student and ktr1.tournament = ktr2.tournament) implies
		    ktr1 = ktr2
}

//The student has KTRank only if he is subscribed to that tournament
fact KTROnlyIfSubscribed{
	all ktr : KTRank , s : Student |
	    ktr.student = s implies
	        isSubscribed[s, ktr.tournament]
}

//The tournament rank for every student in every tournament depends on the sum of the scores of all his teams
fact TournamentRankProperlyBasedOnScore{
	all s1, s2 : Student, kt : KataTournament | 
		(s1 != s2 and isSubscribed[s1, kt] and isSubscribed[s2, kt] and studentScore[s1, kt] <= studentScore[s2, kt]) implies 
			(all ktr1 : getKTRanks[s1] , ktr2 : getKTRanks[s2] | 
				( ktr1.tournament = kt and ktr2.tournament = kt ) implies
				    ktr1.ktRank > ktr2.ktRank)
}

// RUN -----------------------------------------------------------------------------------------------------------------

pred show {
	#Team = 3
}

run show for 10
