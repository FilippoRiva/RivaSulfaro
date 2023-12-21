// +--------------------------------------------+
// |                 Associations               |
// +--------------------------------------------+

//Every codeKata and every team must have different gitHub repository
fact gitHubRepoAreAllDifferent{
	all t : Team, ck : CodeKata |
	    ck.gitHubRepoKata != t.gitHubRepoTeam
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

// +--------------------------------------------+
// |               Int Calculation              |
// +--------------------------------------------+

//The battle rank for every team depends on the score of the team
fact RankProperlyBasedOnScore{
	all t1, t2 : Team | t1 != t2 and
	    t1.kb = t2.kb implies
	        (t1.battleRank != t2.battleRank and
	            (t1.solution.score < t2.solution.score implies
	                t1.battleRank > t2.battleRank))
}

//The tournament rank for every student in every tournament depends on the sum of the scores of all his teams
fact TournamentRankProperlyBasedOnScore{
	all s1, s2 : Student, kt : KataTournament |
		(s1 != s2 and isSubscribed[s1, kt] and isSubscribed[s2, kt] and studentScore[s1, kt] <= studentScore[s2, kt]) implies
			(all ktr1 : getKTRanks[s1] , ktr2 : getKTRanks[s2] |
				( ktr1.tournament = kt and ktr2.tournament = kt ) implies
				    ktr1.ktRank > ktr2.ktRank)
}

//Every team has a number of student that respect the minimum and maximum imposed by the educator
fact ProperTeamSize{
	all kb : KataBattle | all t : getTeams[kb] |
	    #t.players >= kb.minTeamSize and #t.players <= kb.minTeamSize
}